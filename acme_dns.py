#!/usr/bin/env python3
# The original acme-tiny code is Copyright Daniel Roesler under MIT license.
# see LICENSE at github.com/diafygi/acme-tiny
# The acme-dns modifications are Copyright Jon DeVree under MIT license.
# see LICENSE at github.com/nuxi/acme-tiny

from __future__ import print_function

import argparse, subprocess, json, os, sys, base64, binascii, time, hashlib, re, copy, textwrap, logging

import pprint
import six
import socket
import time
import traceback

import dns.message
import dns.name
import dns.query
import dns.rcode
import dns.rdataclass
import dns.rdatatype
import dns.resolver
import dns.update
import dns.tsigkeyring

from six.moves.urllib.request import urlopen, Request

TEST_CA = "https://acme-staging-v02.api.letsencrypt.org/directory"
PROD_CA = "https://acme-v02.api.letsencrypt.org/directory"

# weeee magic numbers!
LE_SHORT_CHAIN = "0"
LE_LONG_CHAIN = "1"

LOGGER = logging.getLogger(__name__)
LOGGER.addHandler(logging.StreamHandler())
LOGGER.setLevel(logging.INFO)

def get_crt(account_key, csr, skip_check=False, log=LOGGER, CA=PROD_CA, chain=None, contact=None,
            dns_server=None, ddns_keyring=None, ddns_algo=None):
    directory, acct_headers, alg, jwk, nonce = None, None, None, None, [None] # global variables

    if dns_server:
        resolver = dns.resolver.Resolver(configure=False)
        resolver.nameservers = dns_server.split(',')
    else:
        resolver = dns.resolver.get_default_resolver()

    # helper functions - base64 encode for jose spec
    def _b64(b):
        return base64.urlsafe_b64encode(b).decode('utf8').replace("=", "")

    # helper function - run external commands
    def _cmd(cmd_list, stdin=subprocess.PIPE, cmd_input=None, err_msg="Command Line Error"):
        proc = subprocess.Popen(cmd_list, stdin=stdin, stdout=subprocess.PIPE, stderr=subprocess.PIPE, close_fds=True)
        out, err = proc.communicate(cmd_input)
        if proc.returncode != 0:
            raise IOError("{0}\n{1}".format(err_msg, err))
        return out

    # helper function - make request and automatically parse json response
    def _do_request(url, data=None, err_msg="Error", depth=0):
        try:
            resp = urlopen(Request(url, data=data, headers={"Content-Type": "application/jose+json", "User-Agent": "acme-tiny-dns"}))
            resp_data, code, headers = resp.read().decode("utf8"), resp.getcode(), resp.headers
        except IOError as e:
            resp_data = e.read().decode("utf8") if hasattr(e, "read") else str(e)
            code, headers = getattr(e, "code", None), {}
        nonce[0] = headers.get('Replay-Nonce', None)
        try:
            resp_data = json.loads(resp_data) # try to parse json results
        except ValueError:
            pass # ignore json parsing errors
        if depth < 100 and code == 400 and resp_data['type'] == "urn:ietf:params:acme:error:badNonce":
            raise IndexError(resp_data) # allow 100 retrys for bad nonces
        if code not in [200, 201, 204]:
            raise ValueError("{0}:\nUrl: {1}\nResponse Code: {2}\nResponse: {3}".format(err_msg, url, code, resp_data))
        return resp_data, code, headers

    # helper function - make signed requests
    def _send_signed_request(url, payload=None, err_msg="Error", depth=0):
        payload64 = _b64(json.dumps(payload).encode('utf8')) if payload is not None else ""
        if nonce[0] is None:
            _do_request(directory['newNonce'])
        protected = {"url": url, "alg": alg, "nonce": nonce[0]}
        protected.update({"jwk": jwk} if acct_headers is None else {"kid": acct_headers['Location']})
        protected64 = _b64(json.dumps(protected).encode('utf8'))
        protected_input = "{0}.{1}".format(protected64, payload64).encode('utf8')
        out = _cmd(["openssl", "dgst", "-sha256", "-sign", account_key], cmd_input=protected_input, err_msg="OpenSSL Error")
        data = json.dumps({"protected": protected64, "payload": payload64, "signature": _b64(out)})
        try:
            return _do_request(url, data=data.encode('utf8'), err_msg=err_msg, depth=depth)
        except IndexError: # retry bad nonces (they raise IndexError)
            return _send_signed_request(url, payload, err_msg, depth=(depth + 1))

    # helper function - poll until complete
    def _poll_until_not(url, pending_statuses, err_msg="Error", timeout=90):
        deadline = time.time() + timeout
        while True:
            result, _, _ = _send_signed_request(url, err_msg=err_msg)
            if time.time() < deadline and result['status'] in pending_statuses:
                time.sleep(2)
                continue
            return result

    # parse account key to get public key
    log.info("Parsing account key...")
    out = _cmd(["openssl", "rsa", "-in", account_key, "-noout", "-text"], err_msg="OpenSSL Error")
    pub_pattern = r"modulus:\n\s+00:([a-f0-9\:\s]+?)\npublicExponent: ([0-9]+)"
    pub_hex, pub_exp = re.search(pub_pattern, out.decode('utf8'), re.MULTILINE|re.DOTALL).groups()
    pub_exp = "{0:x}".format(int(pub_exp))
    pub_exp = "0{0}".format(pub_exp) if len(pub_exp) % 2 else pub_exp
    alg = "RS256"
    jwk = {
        "e": _b64(binascii.unhexlify(pub_exp.encode("utf-8"))),
        "kty": "RSA",
        "n": _b64(binascii.unhexlify(re.sub(r"(\s|:)", "", pub_hex).encode("utf-8"))),
    }
    accountkey_json = json.dumps(jwk, sort_keys=True, separators=(',', ':'))
    thumbprint = _b64(hashlib.sha256(accountkey_json.encode('utf8')).digest())

    # find domains
    log.info("Parsing CSR...")
    out = _cmd(["openssl", "req", "-in", csr, "-noout", "-text"], err_msg="Error loading {0}".format(csr))
    domains = set([])
    common_name = re.search(r"Subject:.*? CN\s?=\s?([^\s,;/]+)", out.decode('utf8'))
    if common_name is not None:
        domains.add(common_name.group(1))
    subject_alt_names = re.search(r"X509v3 Subject Alternative Name: \n +([^\n]+)\n", out.decode('utf8'), re.MULTILINE|re.DOTALL)
    if subject_alt_names is not None:
        for san in subject_alt_names.group(1).split(", "):
            if san.startswith("DNS:"):
                domains.add(san[4:])
    log.info("Found domains: {0}".format(", ".join(domains)))

    # get the ACME directory of urls
    log.info("Getting directory...")
    directory, _, _ = _do_request(CA, err_msg="Error getting directory")
    log.info("Directory found!")

    # create account, update contact details (if any), and set the global key identifier
    log.info("Registering account...")
    reg_payload = {"termsOfServiceAgreed": True}
    account, code, acct_headers = _send_signed_request(directory['newAccount'], reg_payload, "Error registering")
    log.info("{0}egistered: {1}".format("R" if code == 201 else "Already r", acct_headers['Location']))
    if contact is not None:
        account, _, _ = _send_signed_request(acct_headers['Location'], {"contact": contact}, "Error updating contact details")
        log.info("Updated contact details:\n{0}".format("\n".join(account['contact'])))

    # create a new order
    log.info("Creating new order...")
    order_payload = {"identifiers": [{"type": "dns", "value": d} for d in domains]}
    order, _, order_headers = _send_signed_request(directory['newOrder'], order_payload, "Error creating new order")
    log.info("Order created!")

    pending = []

    # get the authorizations that need to be completed
    for auth_url in order['authorizations']:
        authorization, _, _ = _send_signed_request(auth_url, err_msg="Error getting challenges")
        domain = authorization['identifier']['value']
        rdomain = '*.{0}'.format(domain) if authorization.get('wildcard', False) else domain
        if authorization['status'] == 'valid':
            log.info('Existing authorization for {0} is still valid!'.format(rdomain))
            continue
        types = [c['type'] for c in authorization['challenges']]
        if 'dns-01' not in types:
            raise IndexError('Challenge dns-01 is not allowed for {0}. Permitted challenges are: {1}'.format(rdomain, ', '.join(types)))
        log.info("Verifying {0} part 1...".format(rdomain))

        # find the dns-01 challenge and write the challenge file
        challenge = [c for c in authorization['challenges'] if c['type'] == "dns-01"][0]
        token = re.sub(r"[^A-Za-z0-9_\-]", "_", challenge['token'])
        keyauthorization = "{0}.{1}".format(token, thumbprint)
        record = _b64(hashlib.sha256(keyauthorization.encode('utf8')).digest())
        log.info('_acme-challenge.{0}. 60 IN TXT {1}'.format(domain, record))
        pending.append((auth_url, authorization, challenge, domain, keyauthorization, rdomain, record, token))

    if pending:
        if not ddns_keyring:
            log.info('Press enter to continue after updating DNS server')
            six.moves.input()
        else:
            log.debug('Performing DNS Zone Updates...')
            for authz in pending:
                auth_url, authorization, challenge, domain, keyauthorization, rdomain, record, token = authz
                zone = str(dns.resolver.zone_for_name('_acme-challenge.{0}'.format(domain), resolver=resolver))
                master = str(resolver.resolve(zone, 'SOA')[0].mname)
                try:
                    server = str(resolver.resolve(master, 'A')[0].address)
                except dns.resolver.NoAnswer:
                    server = str(resolver.resolve(master, 'AAAA')[0].address)
                log.debug('Updating TXT record _acme-challenge.{0} in DNS zone {1} on {2}'.format(domain, zone, master))
                update = dns.update.Update(zone, keyring=ddns_keyring, keyalgorithm=ddns_algo)
                update.replace('_acme-challenge.{0}.'.format(domain), 60, 'TXT', str(record))
                response = dns.query.tcp(update, server, timeout=10)
                if response.rcode() != 0:
                    raise Exception("DNS zone update failed, aborting, query was: {0}".format(response))
            time.sleep(7)

    # verify each domain
    for authz in pending:
        auth_url, authorization, challenge, domain, keyauthorization, rdomain, record, token = authz

        log.info("Verifying {0} part 2...".format(rdomain))

        if not skip_check:
            # check that the DNS record is in place
            zone = dns.resolver.zone_for_name(domain, resolver=resolver)

            master = set()
            for family in resolver.resolve_name(resolver.resolve(zone, 'SOA')[0].mname).values():
                master = master.union(map(str, family))

            addr = set()
            for x in resolver.resolve(zone, 'NS'):
                addr = addr.union(map(str, resolver.resolve(str(x), 'A', raise_on_no_answer=False)))
                addr = addr.union(map(str, resolver.resolve(str(x), 'AAAA', raise_on_no_answer=False)))

            if not addr:
                raise ValueError("No DNS server for {0} was found".format(domain))

            qname = '_acme-challenge.{0}'.format(domain)
            valid = []
            for x in addr:
                errmsg = None
                req = dns.message.make_query(qname, 'TXT')
                try:
                    resp = dns.query.udp(req, x, timeout=30)
                except socket.error as e:
                    errmsg = 'Exception contacting {0}: {1}'.format(x, e)
                except dns.exception.DNSException as e:
                    errmsg = 'Exception contacting {0}: {1}'.format(x, e)
                else:
                    if resp.rcode() != dns.rcode.NOERROR:
                        errmsg = "Query for {0} returned {1} on nameserver {2}".format(qname, dns.rcode.to_text(resp.rcode()), x)
                    else:
                        answer = resp.get_rrset(resp.answer, dns.name.from_text("{0}.".format(qname.rstrip(".")), None),
                                                dns.rdataclass.IN, dns.rdatatype.TXT)
                        if answer:
                            txt = list(map(lambda x: str(x)[1:-1], answer))
                            if record not in txt:
                                errmsg = "{0} does not contain {1} on nameserver {2}".format(qname, record, x)
                            else:
                                valid.append(x)
                        else:
                            errmsg = "Query for {0} returned an empty answer set on nameserver {1}".format(qname, x)

                if errmsg is not None:
                    # If the DNS resolver is overriden then there is a good chance that not all the servers
                    # can be reached. So when the resolver is overriden, only treat errors communicating with
                    # the master as errors.
                    if dns_server is None or x in master:
                        raise ValueError(errmsg)
                    else:
                        log.warning(errmsg)

            if not valid:
                raise ValueError("No DNS server for {0} was reachable".format(qname))

        # say the challenge is done
        _send_signed_request(challenge['url'], {}, "Error submitting challenges: {0}".format(rdomain))

        # skip checking challenge state because it won't change if another challenge for this authorization has completed
        authorization = _poll_until_not(auth_url, ["pending"], "Error checking authorization status for {0}".format(rdomain))
        if authorization['status'] != "valid":
            errors = [c for c in authorization['challenges'] if c['status'] not in ('valid', 'pending') and 'error' in c]
            dns_error = [c for c in errors if c['type'] == 'dns-01']

            reason = dns_error[0] if dns_error else errors[0] if errors else None
            if reason is not None:
                raise ValueError("Challenge {0} failed (status: {1}) for {2}:\n{3}".format(reason['type'], reason['status'], rdomain,
                                 pprint.pformat(reason['error'])))
            else:
                raise ValueError("Authorization failed for {0}:\n{1}".format(rdomain, pprint.pformat(authorization)))
        log.info("{0} verified!".format(domain))

    # poll the order to monitor when it's ready
    order = _poll_until_not(order_headers['Location'], ["pending"], "Error checking order status")
    if order['status'] != "ready":
        raise ValueError("Order failed: {0}".format(order))

    # finalize the order with the csr
    log.info("Signing certificate...")
    csr_der = _cmd(["openssl", "req", "-in", csr, "-outform", "DER"], err_msg="DER Export Error")
    _send_signed_request(order['finalize'], {"csr": _b64(csr_der)}, "Error finalizing order")

    # poll the order to monitor when it's done
    order = _poll_until_not(order_headers['Location'], ["ready", "processing"], "Error checking order status")
    if order['status'] != "valid":
        raise ValueError("Order failed: {0}".format(order))

    # download the certificate
    cert_url = "{}/{}".format(order['certificate'], chain) if chain is not None else order['certificate']
    certificate_pem, _, cert_headers = _send_signed_request(cert_url, err_msg="Certificate download failed")
    if cert_headers['Content-Type'] != "application/pem-certificate-chain":
        raise ValueError("Certifice received in unknown format: {0}".format(cert_headers['Content-Type']))

    # the spec recommends making sure that other types of PEM blocks don't exist in the response
    prefix = "-----BEGIN "
    suffix = "CERTIFICATE-----"
    for line in certificate_pem.splitlines():
        if line.startswith(prefix) and not line.endswith(suffix):
            raise ValueError("Unexpected PEM header in certificate: {0}".format(line))

    log.info("Certificate signed!")

    if pending:
        if not ddns_keyring:
            log.debug("You can now remove the _acme-challenge records from your DNS zone.")
        else:
            log.debug('Removing DNS records added for ACME challange...')
            for authz in pending:
                auth_url, authorization, challenge, domain, keyauthorization, rdomain, record, token = authz
                zone = str(dns.resolver.zone_for_name('_acme-challenge.{0}'.format(domain), resolver=resolver))
                master = str(resolver.resolve(zone, 'SOA')[0].mname)
                try:
                    server = str(resolver.resolve(master, 'A')[0].address)
                except dns.resolver.NoAnswer:
                    server = str(resolver.resolve(master, 'AAAA')[0].address)
                log.debug('Updating TXT record _acme-challenge.{0} in DNS zone {1} on {2}'.format(domain, zone, master))
                update = dns.update.Update(zone, keyring=ddns_keyring, keyalgorithm=ddns_algo)
                update.delete('_acme-challenge.{0}.'.format(domain), 'TXT')
                response = dns.query.tcp(update, server, timeout=10)

    return certificate_pem

def main(argv=None):
    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=textwrap.dedent("""\
            This script automates the process of getting a signed TLS certificate from Let's Encrypt using
            the ACME protocol. It will need to be run on your server and have access to your private
            account key, so PLEASE READ THROUGH IT!

            This version has been modified from the original to use DNS challenge instead of HTTP

            Example Usage:
            python acme_dns.py --account-key ./account.key --csr ./domain.csr > signed_chain.crt
            """)
    )
    parser.add_argument("--account-key", required=True, help="path to your Let's Encrypt account private key")
    parser.add_argument("--csr", required=True, help="path to your certificate signing request")
    parser.add_argument("--quiet", action="store_const", const=logging.ERROR, help="suppress output except for errors")
    parser.add_argument("--skip", action="store_true", help="skip checking for DNS records")
    parser.add_argument("--disable-check", dest='skip', action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--no-chain", action="store_true", help="Do not print the intermediate certificates")
    parser.add_argument("--chain", default=None, help="Select certificate chain ('short' or 'long')")
    parser.add_argument("--ca", default=PROD_CA, help="certificate authority, default is Let's Encrypt Production")
    parser.add_argument("--directory-url", dest='ca', help=argparse.SUPPRESS)
    parser.add_argument("--contact", help="an optional email address to receive expiration alerts from Let's Encrypt")
    parser.add_argument("--dns-server", metavar='DNS_SERVER', help="optional. Recursive DNS server to use. Which can be needed when there is a different internal DNS view.")
    parser.add_argument("--ddns-key", nargs=3, metavar=('KEY_NAME','SECRET','ALGORITHM'), help="optional. The key name, secret and algorithm for the TSIG key which may be used to authenticate the DNS zone updates")

    args = parser.parse_args(argv)

    ddns_algo = None
    ddns_keyring = None
    if args.ddns_key:
        ddns_keyring = dns.tsigkeyring.from_text({args.ddns_key[0]:args.ddns_key[1]})
        ddns_algo = args.ddns_key[2]

    LOGGER.setLevel(args.quiet or LOGGER.level)

    if args.ca.upper() in ('PRODUCTION', 'PROD', 'DEFAULT') or args.ca == PROD_CA:
        ca = PROD_CA
        LOGGER.info("Using Let's Encrypt production CA: {0}".format(ca))
    elif args.ca.upper() in ('TEST', 'STAGING', 'DEVEL', 'DEV') or args.ca == TEST_CA:
        ca = TEST_CA
        LOGGER.info("Using Let's Encrypt staging CA: {0}".format(ca))
    else:
        ca = args.ca
        LOGGER.info("Using other CA: {0}".format(ca))

    no_chain = args.no_chain
    chain = None
    if ca in (PROD_CA, TEST_CA):
        if args.chain is not None:
            if args.chain.upper() in ('SHORT', 'ISRG'):
                chain = LE_SHORT_CHAIN
                LOGGER.info("Forcing Let's Encrypt short chain (ISRG root)")
            elif args.chain.upper() in ('LONG', 'DST'):
                chain = LE_LONG_CHAIN
                LOGGER.info("Forcing Let's Encrypt long chain (DST root)")
            elif args.chain.upper() in ('NONE', 'NO'):
                no_chain = True
                pass
            else:
                try:
                    int(args.chain)
                except ValueError:
                    parser.error("Invalid Let's Encrypt chain specified: {0}".format(args.chain))
                chain = args.chain
                LOGGER.info("Using alternate chain: {0}".format(chain))
    else:
        chain = args.chain
        LOGGER.info("Using alternate chain: {0}".format(chain))

    signed_crt = get_crt(args.account_key, args.csr, args.skip, log=LOGGER, CA=ca, chain=chain, contact=args.contact,
                         dns_server=args.dns_server, ddns_keyring=ddns_keyring, ddns_algo=ddns_algo)

    end = "-----END CERTIFICATE-----"
    for line in signed_crt.splitlines():
        sys.stdout.write('{0}\n'.format(line))
        if no_chain and line == end:
            break

if __name__ == "__main__": # pragma: no cover
    main(sys.argv[1:])
