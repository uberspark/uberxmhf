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

## V0.5: pal generates audit-string instead of parsing an untrusted auditable command string

R->P cmd-id, cmd-params
P: pending-cmd-handle = next-pending-cmd-handle++
   pending-cmds[pending-cmd-handle] = {
      pending-cmd-id = cmd-id
      pending-cmd-params = cmd-params
      audit-nonce = gen-non-repeating-nonce()
      audit-string = gen-audit-string(cmd-id, cmd-params)
      t0=gettime()
   }
P->R audit-nonce, audit-string, pending-cmd-handle
R->A audit-nonce, audit-string
A: record audit-nonce, audit-string, current-server-time, ...
   audit-token=S_A(audit-nonce||audit-string)
A->R audit-token
R->P audit-token pending-cmd-handle
P: if (gettime() - t < threshold
       && Verify_A(audit-nonce||audit-string, audit-token))
       audit-nonce=nil
       t0=nil
       Execute(pending-cmd-id, pending-cmd-params)
       pending-cmd-id = nil
       pending-cmd-params = nil

## V1, add authentication of PAL to audit server

R->P cmd-id, cmd-params
P: quote-cert-chain = svc-get-cert-chain()
   pending-cmd-handle = next-pending-cmd-handle++
   pending-cmds[pending-cmd-handle] = {
      pending-cmd-id = cmd-id
      pending-cmd-params = cmd-params
      audit-nonce = gen-non-repeating-nonce()
      audit-string = gen-audit-string(cmd-id, cmd-params)
      t0=gettime()
      quote = svc-gen-quote(pcrs=0, nonce=H(audit-nonce || audit-string || quote-cert-chain(?) || ?))
   }
P->R audit-nonce, audit-string, quote, quote-cert-chain, pending-cmd-handle
R->A audit-nonce, audit-string, quote, quote-cert-chain
A: record audit-nonce, audit-string, quote, quote-cert-chain, current-server-time, ...
   audit-token=S_A(audit-nonce||audit-string)
A->R audit-token
R->P audit-token, pending-cmd-handle
P: if (gettime() - t < threshold
       && Verify_A(audit-nonce||audit-string, audit-token))
       audit-nonce=nil
       t0=nil
       Execute(pending-cmd-id, pending-cmd-params)
       pending-cmd-id = nil
       pending-cmd-params = nil

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
_audited-kv_ : Provides an audited key-value store. Mostly wrappers
          around PAL code to deal with (un)registration and (un)marshalling.
_audited-kv-pal_ : the PAL code that actually runs inside the TEE
          to implement the audited key-value store.

# Misc Notes

## Command string vs Audit string

2011-06-08: actually, let's have the pal generate the command string
and return it to the program. This avoids all the complexities and
pitfalls of having the PAL try to parse an untrusted human-readable
command string. Instead, think of this as an *audit string*; the
program gives the PAL a command it would like to execute, and the PAL
returns a string that the program must prove is audited before the PAL
will execute the command.

## Reentrancy

2011-06-08: let's make the PAL reentrant. Instead of storing the
audit-nonce, audit-string, time, etc., let's seal it for ourselves and
make the calling program give it back to us when it wants to execute
the command. we'll need the pcr-at-origin feature in seal to validate
this data. 

XXX - nope, won't work. This would allow unlimited replay of a command
within the audit-time-threshold. Let's just store the state inside the
PAL instead. It can be non-reentrant for now. Later we can have the
PAL store the state for several outstanding requests.

We *could* only store the audit-nonces inside the PAL and have the
regular program store the rest of the saved data for us. This would
reduce the memory requirement inside the PAL, but wouldn't really
simplify anything since we'd still need to keep track of pending
audit-nonces inside the PAL.

## Human-readable vs compact command\audit strings

In terms of efficiency, it might make more sense for the string sent
to the audit-server to be in a "binary" format. Since the audit server
is trusted, we can trust it to faithfully convert the binary format to
a human-readable format.

The down-side to this design is that the audit-server must then
understand the binary format. I would prefer to keep the audit-server
as generic as possible, so that it can support other pals using this
auditable-command model without having to know anything about each
one.

We *could* have the audit server just return the opaque binary blob
when audit logs are requested, and use local processing to convert it
to human-readable format. This is a bit of a pain though, since you
wouldn't be able to access the logs from just any machine.

## How large does the audit nonce need to be?

The attacker model is that the malware-attacker has a set of
audit-tokens for a command that was previously executed. The attacker
wants to keep initiating that command with the PAL again until the PAL
generates an audit-nonce matching one of the audit-tokens. This part
seems like a birthday-attack, which implies we'd need something on the
order or 256 bits for the audit nonce _if the pal generates the audit
nonces uniformly at random_.

On the other hand, the nonces do not really need to be random. They
just need to not repeat. Can we do this by making them monotonic?

I think we can do this by simply using the epoch-nonce + relative time
obtained from the svcapi. In the current version of the protocol, we
could set the audit-nonce to epoch-nonce||epoch-offset.

It might make sense for this to be a "first class" concept
though. i.e., this is more information that would be useful in the
audit log. Therefore, we could actually _replace_ the audit-nonce with
epoch-nonce and epoch-offset.
