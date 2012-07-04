Sealing and Attestation
=======================

Last updated: 2012-07-03.

TrustVisor support for Micro-TPM Sealing: Initialization and Steady-State
-------------------------------------------------------------------------

* The NV Index is defined by untrusted code running on the ordinary OS.  For example, using the open-source jTpmTools + jTSS.

    `jtt nv_definespace --index 0x00011337 --size 20 -o tpm -e ASCII -p 17,18 -w --permission 0x00000000 --writelocality 2 --readlocality 2`

* Inside TrustVisor, we need some default NV index to use if none is supplied.  Let's use 0x00015213 as a tribute to CMU's zip code.
    * No problem with the index being overridden on the boot command line (and really, it's an input parameter for the SL/Runtime, so during dynamic launch it can be a component of whatever parameter block definition we eventually choose).

* During TrustVisor runtime initialization's master crypto initialization, we deal with the long-term Micro-TPM sealing keys.
    1. If no index is provided or the provided index does not point to a defined space, *goto Handle-Failure*.
    + Interrogate the defined region for appropriate size and access controls.  These should be: 20 bytes; and the value of PCRs 17 and 18, and precisely Locality 2 for both reading and writing.  If anything else is detected, ***goto Handle-Failure***.
    + Read the value from the defined region.  If it is "all bits set" (0xff repeating), this is an indication that the index is newly defined and has never been written.
    + ***Handle-Failure:*** Either (1) *Halt* or (2) *Print a loud warning* and continue in "ephemeral mode", where PALs will operate but sealed data will become irretrievable across reboots.
    + Get some random bytes from the hardware TPM and write them into the region (unless we're in ephemeral mode). Call them the *MasterSealingSecret*.
    + Derive the sealing encryption and MAC keys from the MasterSealingSecret.


* During TrustVisor startup, if no NVRAM Index containing the master seed for Micro-TPM sealing support is found (may be necessary to specify this as a boot parameter, or have some default that can be overridden by a boot parameter), then generate a new MasterSecret and derive the long-term encryption and MAC keys.

### Convenience / Streamlining feature possibilities for the future ###

* TrustVisor doesn't know the TPM's owner secret so it cannot create the relevant NVRAM index on its own.
    * If no NV Index is defined (or if it is defined incorrectly), development can proceed and PALs using Micro-TPM sealed storage will work, but sealed data will become irretrievable after a platform reboot (because the MasterSealingSecret is ephemeral and is lost at reboot).
* If a special hypercall is invoked that includes the TPM's Owner Secret (or if it is provided on the command line to TrustVisor at boot time), then TrustVisor can setup the necessary NVRAM index based on TrustVisor's own code identity and access-controlled by physical TPM PCR values.  This will require significant additional implementation of hardware TPM commands inside TrustVisor. For the time being we have decided against this strategy and require a Linux guest OS to define the relevant regions in a trust-on-first-use model.

Long-term TrustVisor state
--------------------------

* Symmetric cryptographic keys that provide secrecy and integrity-protection for micro-TPM sealed storage. Both derived from a master secret that resides in hardware TPM NVRAM and accessible only to TrustVisor.
* No automated tagging of sealed data with the registered code for the corresponding PAL.  A PAL should include the uPCR-0 that represents its own code identity if this property is desired.
    * Because a micro-TPM instance is always created through registration which resembles dynamic root of trust, we always have a code-identity measurement that we can depend on.
* Data sealed on one platform will never unseal on a different physical platform (much like real TPM-sealed data) because the sealing encryption/MAC keys are secret, unique, and platform-specific.
* If multiple instances of an identical PAL are registered, they will be able to unseal each other's sealed data.  This is not a new problem, i.e., the same issue exists with Flicker.  However, now we can have multiple truly concurrent PALs.
    * I don't think this matters at all.  If the actions taken in the set of identical PALs are thread-safe and hence serializable, then they are equivalent to some number of individual Flicker sessions.  Coping with "parallel session" types of attacks is necessary at a higher level, i.e., the PAL developer must take responsibility for this.  It would be great to develop a library to relieve the actual non-expert developer from this burden, but with respect to layers of abstraction from TrustVisor's perspective handling this interleaving securely is the PAL's responsibility.
    * Well, it probably means the Micro-TPM interface needs to be thread-safe.

Hardware TPM Attestation
------------------------

* Ordinary TPM-based attestation to the dynamic launch of TrustVisor convinces a remote party that a particular host is running TrustVisor.  Hosts are authenticated via a TPM AIK.  It can be certified using a PrivacyCA or we can short-circuit the Privacy CA path and use the EK Cert directly as the platform ID.
    *  This does not require much new development at all.  Existing attestation protocols should work just fine. Further, the desired security properties of secrecy and integrity are maintained even if AIK(s) and TPM Quote generation are entirely managed by untrusted code (this is the beauty of a dedicated hardware root of trust).
* See `tee-sdk/examples/attestation` for an example.

Certifying a Micro-TPM
----------------------

* The ability to certify a micro-TPM as a valid micro-TPM instance running on top of TrustVisor.
* GOAL: Unlinkability of Micro-TPM attestation (between potentially mutually distrusting PALs) / privacy protection that is at least as good as that available to hardware TPM via an AIK.
* The Micro-TPM needs its own signing keypair(s) that will be used to sign attestations.  This suggests some level of key generation support.
    * TrustVisor needs to be able to sign something indicating that a micro-TPM is valid.  TrustVisor could (1) use a TPM-based key for this, or (2) generate its own software-based keypair, or (3) generate an ephemeral software-based or TPM-based keypair.
        * Call this keypair *TvHwSwBridgeSigner*.
    * *Privacy Concern*: A single *TvHwSwBridgeSigner* links all PAL attestations to the same physical platform.  Thus, with a single *TvHwSwBridgeSigner*, there is no advantage to having a separate signing keypair for each micro-TPM instance.
        * Soln (1) is compelling because it provides maximal protection for the private key, but it is slow.  This is only viable if such signatures are expected to be rare.
            * A further challenge is dealing with finite TPM keyslots while playing nice with legacy OS TPM drivers.  See [tickets:#15].
        * Soln (2) is compelling because *TvHwSwBridgeSigner* can be derived from a single 20~40 byte master secret, which enables the only non-volatile state required by TrustVisor to be the master-secret, instead of the output of one or more TPM Seal operations (e.g., if we used a TPM-based key nested under the SRK).  Let's call this the *Small-State-Trick*. This space-saving is important in the case where we use the TPM's limited non-volatile storage to persist trustvisor's state. Pros: smaller state, faster private key operations.  Cons: key lives in DRAM, not in TPM. (Summarized another way: Actual TPM keys end up as ciphertext that must be persisted; using our own key generated based on the small MasterSecret that is easier to persist might be more practical for now.)
        * Soln (3) is compelling because it simplifies development for the time being.  A new attestation would be required every time the platform running TrustVisor reboots. With  dynamic re-loading (someday, when it's implemented), we have a presence (e.g., daemon) in the untrusted OS that can seal/unseal the per-physical-boot ephemeral keypair, thereby eliminating the cost.
    * *Quick and Dirty*: If we relax the Privacy / Unlinkability requirement, we can collapse the certification chain for a micro-TPM quote into a single signature from a single keypair maintained inside TrustVisor.  Because there is only one, it can be extended directly into one of the dynamic PCRs inside of TrustVisor itself. We can persist it across dynamic reloads (a la (3) above) if desired as a performance optimization.
    * *Don't Forget*:
        * Hard part of uTPM quote signing key certification is to link it to the physical TPM's active AIK without allowing quotes from different uTPM instances to be linked, and without trusting the code running on the untrusted OS. (This invalidates solutions such as hashing the active public AIK and using that as part of the quote nonce.)
        * This gives rise to the requirement of a per-micro-TPM-instance TrustVisor signing ability, since any unified signing ability would implicitly link uTPM instances to the same TrustVisor instance.

Micro-TPM Identity Key Design Challenges
----------------------------------------

* How many identity keys can a micro-TPM have? (The answer will be either "exactly one" or "an arbitrary number".)
    * With the *Quick and Dirty* trick, a micro-TPM will only ever have one active identity key, and that keypair is dictated by TrustVisor itself. The micro-TPM has no say in it.
    * *Multiple Identity Keys for Micro-TPMs?*
        * GenerateSigningKey: Cause the micro-TPM to discard the current signing keypair and generate a new one.
        * ExportSigningKey: Cause the micro-TPM to somehow encrypt the current signing keypair so that it can be reloaded later (e.g., after a power cycle).  It becomes the PAL's responsibility to see that the ciphertext is persisted using some kind of non-volatile storage (e.g., the untrusted OS's filesystem + disk).
    *    * *Challenge:* This is effectively "sealing" that signing key.  What should it be sealed to?  Should it take PCR specifications like the Micro-TPM's sealing API? Probably. *XXX TODO XXX*
        * ImportSigningKey: Cause the micro-TPM to reload a previously exported signing keypair.
* What if the identical PAL is registered multiple times?
* How do we isolate the relevant micro-TPM instances?

Micro-TPM Design and API
========================

Hardware TPM Compatibility
--------------------------

* *Design Question:* Should the uTPM look like a stripped down TPM, or should we break compatibility with existing TPM software?
* *Decision: Break compatibility*.  We are interested in minimal size and design simplicity above all for the uTPM.  A "compatibility layer" to bridge things to, e.g., an application compiled against a TSS library, can be written later. newlib + libnosys + ibmswtpm can likely provide a full software v1.2 TPM implementation with manageable effort.

Micro-TPM API / Provided Functionality
--------------------------------------

### PCR Read / Extend (easy) ###

* Read or extend the appropriate uPCR in the proper uTPM instance. *Done.*

### GetRandom (easy) ###

* A PAL needs a source of random numbers to use as nonces, keys, etc.
* These random numbers are provided by TrustVisor.  The most likely design is to seed a PRNG with high-quality randomness from the v1.2 hardware TPM's GetRandom facility when TrustVisor boots / initializes (if it is launched late).
    * A shortcut with a performance hit is just to call the real TPM's GetRandom facility every time.  This may introduce contention with the TSS (e.g., TrouSerS / tcsd) in the legacy OS though.
* Implemented CTR_DRBG with AES-256 as PRNG, using TPM Entropy for instantiation and reseeding. *Done.*

### Quote (Moderate) ###

* This one is tricky. Many of the issues mentioned here: [Hardware TPM Usage and Design]
* *Quick and Dirty* version (one single, ephemeral, bridge signing keypair for a TrustVisor boot cycle) *Done.*


### Seal / Unseal (Moderate) ###

* Sealing is performed using long-term symmetric keys maintained by logic that is part of TrustVisor.  Ciphertexts sealed by different PALs will be encrypted and integrity protected using the same keys, though the associated uPCRs will be different.
* We mimic the v1.2 hardware TPM's DigestAtCreation and DigestAtRelease data structures, leveraging the individual PAL's uTPM's bank of uPCRs. *Done.*

Internal rollback prevention for TrustVisor
===========================================

* *Design Question:* Does TrustVisor need to protect its own long-term sealing encryption and MAC keys (which are derived from a single master secret) from a rollback attack?
* *Decision: No.* The long-term sealing encryption and MAC keys fulfill the same role as the Storage Root Key (SRK) in the hardware TPM.  The semantics here should be similar.  "Initializing" TrustVisor on a platform (in practice: defining a TPM NVRAM index and locking it to the relevant measurement of TrustVisor, and generating and writing the above-mentioned master secret) is similar to "Taking Ownership" of a hardware TPM.  There is no way to refresh the SRK in a hardware TPM without taking ownership again and losing all previously sealed data.  And so it shall be with Initializing NVRAM for TrustVisor.  Otherwise we have a "turtles all the way down" situation.

### NV DefineSpace / Read / Write (Moderate) ###

* Micro-TPM Seal / Unseal are vulnerable to state rollback attacks.
    * Note that the protocols in [Memoir](http://www.ece.cmu.edu/~jmmccune/memoir/) do not directly apply.  Memoir as described in the paper assumes all PAL state must be serialized and sealed between every invocation.  That is not that case for a PAL on top of TrustVisor, since invocations and registration are distinct.  Such rollback protections are only necessary between *Registrations*, since PAL state cannot be manipulated by untrusted code between *Invocations*.
* The availability of some NV space dedicated to a single PAL can alleviate this, e.g., using a hash chain to keep track of previous state updates while retaining crash resilience.
* *Design Question*: How much responsibility should TrustVisor have to resist rollback attacks against PAL state?
* *Decision: Bare Minimum*. If TrustVisor can expose a small amount of the actual TPM's NV space and offer it to a PAL then that PAL can implement its own Rollback protection.  In practice this can easily be a library against which other PAL authors can link.

NV Multiplexing ("Mux") PAL
---------------------------

* There is very little NV RAM available in today's TPMs.  It is unreasonable to assume that the available TPM NV space is sufficient for a practical number of PALs.  Thus, one of the first PALs to implement is one to offer virtual NV space. There will be a performance hit and the NV PAL will require an untrusted userspace daemon to help serialize and persist things to disk in the untrusted world, but things should scale much better.
* `tee-sdk/examples/rollback` is where this development is taking place.  *Work-in-progress*

PAL-to-PAL communication
------------------------

* The above Seal / Unseal design implies that one PAL *can* seal data for another PAL on the same platform.  Indeed, at the present time, that is the best PAL-to-PAL communication mechanism that we have.  It involves sending the ciphertext from "PAL A" out to "App A", then from "App A" to "App B", then from "App B" to "PAL B".  It's circuitous and likely bad for performance, but for the moment it maintains the desired security properties and the PAL code itself can remain uncomplicated.

Hardware TPM NVRAM
==================

* We use NVRAM for several purposes, which are summarized here.
    * Store the long-term master seed from which encryption and MAC keys for Micro-TPM sealing are derived.
    * Implement rollback protection for the state of one privileged PAL (the "NV Mux PAL")
        * Integrity-checking mechanisms for identifying this PAL are currently based on boot-time command-line parameters to TrustVisor.
        * A reasonable alternative may be that a public key gets embedded in TrustVisor and a suitable NV Mux PAL gets "blessed" by being signed.  This is probably a decent design for TrustVisor upgrades / patches as well, so it should get worked out in that larger context.

Fallen Stars (Stuff that sounded good but turns out to not work)
================================================================

* What do we need to persist micro-TPM instances?
    * This is the wrong question.  A micro-TPM instance lasts only as long as a PAL is registered.  For sealed data to persist, the relevant "storage key(s)" need to somehow persist.  For TrustVisor, this is the symmetric encryption / MAC keys derived from a long-term master seed kept in TPM NVRAM accessible only to TrustVisor.
    * *Rich identity key support for PALs may revive this question.*

* OpenPTS: Open Platform Trust Services [http://sourceforge.jp/projects/openpts/] is the most mature open source project for exchanging additional data with a TPM Quote (i.e., really doing attestations).  It is also worth familiarizing oneself with the TrouSerS "testsuite": [http://trousers.cvs.sourceforge.net/trousers/].  However, neither of these offer sufficient functionality as to solve any of our problems directly.
    * Intel has recently released their [OpenAttestation](https://github.com/OpenAttestation/OpenAttestation) project, which is similar in spirit.  Worth investigating.

* Attempts to mitigate Linkability of multiple Micro-TPM instances via Certification process (we're currently using the Quick and Dirty solution, proposed above, which suffers from this problem)
    * Can we use the single resettable PCR in the hardware TPM?  Likely would would require manipulation of (1) the TOSPresent bit inside the hardware TPM, and (2) the ability of TrustVisor to block the guest OS from invoking any hardware TPM commands while the resettable PCR was reset and re-extended with the current (per-PAL)  TvHwSwBridgeSigner keypair.
        * (Zongwei) *A possible way of doing this may be relying on TPM locality*. TPM locality 2 can reset and extend PCR 20-22, while locality 1 can only extend PCR 20. TrustVisor can protect the I/O physical page (see below) of locality 2 (and above) from the guest OS, and let OS only access locality 1. TrustVisor also need to interpose all guest os access to higher locality and return errors.
        * Some (unverified) information about TPM locality
<pre>
Locality   I/O address    Resettable PCRs  Extendable PCRs
  Any       -             16,23            16,23
  0         FED40000      none             0-15
  1         FED41000      none             20
  2         FED42000      20-22            17-22
  3         FED43000      none             17-20
  4         FED44000      17-20            17,18
</pre>
    * TOS bit: According to TPM PC client spec, it is used to control the behavior of resettable PCRs (17-22). If TOS bit is false, PCR 17-22 will be reset to -1; otherwise, 0.
    * *Can TPM audit session help us in detecting unintended PCR extend?* No, TPM has an internal audit digest (AD), an internal audit monotonic counter (AMC), and an external audit log (AL). AL records the hashes of all audited events since audit session starts. AD holds the hash of external AL. AMC is for sequencing audited events. When an audit session closes, the TPM will sign the concatenation of AD, AMC and AL. The owner of TPM can change which event is audited. With the audit session, we can detect PCR extend operation. However, *because the PCR extend operations is not authenticated, we still don't know whether an extend to PCR 20 of locality 2 is from TV or untrusted OS*. In addition, OS is the owner of TPM, so it can change the behavior of audit session. Thus, audit session may not help us here.

