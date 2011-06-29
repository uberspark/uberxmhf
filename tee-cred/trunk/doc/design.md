This is a general credential management application targeted for
"legacy" applications where we don't know how to pass a credential
directly to the remote server. Instead, we let the untrusted host
handle the necessary credentials on-demand. However, we enforce
some controls including:

* _auditing_ to a remote server. any sensitive operations (such as
   retrieving a credential) cannot be done without first ensuring the
   operation is logged at a trusted audit server. This can help alert
   the user in the case that malware proactively asks for credentials.
* _rate limiting_ to make it more difficult or noticeable for malware
   to pull all of the stored credentials out.
* _local database lock_ the user must provide some master password to
   "unlock" the database for some amount of time (or some number of
   credential requests?). guesses at this master password are
   rate-limited.
* _two-factor authentication_ In the simple case, the audit server is
   a "dumb" logging and timestamping service. The PAL only requires
   proof that an operation is logged before it is willing to perform
   it. However, the audit server can also provide a second level of
   access control and refuse to give the required "audit token" unless
   some other conditions are met. For example, the audit server could
   send a message to the user's cell phone for confirmation in case of
   particularly sensitive operations (full export of the database).

# Protocol

## V0, timestamp server

With R as the regular program, P as the pal, and A as the audit server:

In the first version of the protocol, the PAL does not take any part
in authenticating itself to the audit server (though the audit server
might require the regular program to authenticate itself to provide
access to its timestamping service). The resulting property is that
any "auditable command" executed by the PAL was seen by the audit
server.

R->P get-challenge
P: audit-nonce=getrand()
   t0=gettime()
P->R audit-nonce
R->A auditable-command-string, audit-nonce
A: optionally authenticate R
   record auditable-command-string, audit-nonce, current-server-time
   audit-token=S_A(auditable-command-string || audit-nonce)
A->R audit-token
R->P auditable-command-string, audit-token
P: if (gettime() - t < threshold
       && Verify_A(auditable-command-string || audit-nonce, audit-token))
       audit_nonce=nil
       t0=nil
       Execute(auditable-command-string)

## V1, add authentication of PAL to audit server

Having the PAL not authenticate itself presents a couple
problems. Suppose that the audit server is a shared service. In that
case, *accessing* the audit logs will likely require some
credential. While the above protocol guarantees that auditable
commands are logged at the audit server, it does not guarantee that
the user will be able to access those records. In particular, malware
can create its own account with the audit service, and its commands
logged under its own account rather than the user's account, thus
preventing the user from ever knowing about those events.

In principle this could be worked around in the V0 protocol by the
audit-server having a per-user-account signing key. However, there is
another problem:

The V0 protocol doesn't prevent the attacker from logging arbitrary
commands at the audit server. Technically this doesn't break the
property that "all auditable commands are recorded at the audit
server", however filling the log with false commands could lead to
some confusion by the user.

To address both of these problems, we have the pal authenticate itself
to the audit server, including a quoted measurement of its code image,
and the chain of quotes and certificates necessary to link that quote
with a hardware platform and the software stack running underneath
(e.g., a hardware tpm, a particular version of trustvisor, and a
particular version of the pal itself).

# Software architecture

_tcm_   : top level of the tee credential manager library. This will
          be called by some front-end (e.g., a browser plugin),
          and handles coordinating between the audit server and pal.
_audit_ : handles communication with an audit-server. implemented as a
          pluggable interface such that we can swap out the audit
          module at compile time. The 'testing' version will probably
          just implement the audit server directly. Later versions will
          actually communicate with a remote server.
_tee-cred-pal_ : A pal that protects the credentials. It provides basically
          a key-value store. It requires audit-tokens for most commands.
