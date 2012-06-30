Introduction
============

Lockdown provides the user with a red/green system: an isolated and
constrained environment for performing online transactions, as well as
a high-performance, general-purpose environment for all other
(non-security-sensitive) applications. An external device verifies
which environment is active and allows the user to securely learn
which environment is active and to switch between them.

The original design and implementation of Lockdown is described in:

* Lockdown: Towards a Safe and Practical Architecture for Security
  Applications on Commodity Platforms.  Amit Vasudevan and Bryan Parno
  and Ning Qu and Virgil D. Gligor and Adrian Perrig. Proceedings of
  the 5th International Conference on Trust and Trustworthy Computing
  (TRUST), June 2012.

* Lockdown: A Safe and Practical Environment for Security Applications
  (CMU-CyLab-09-011) Amit Vasudevan and Bryan Parno and Ning Qu and
  Virgil D. Gligor and Adrian Perrig. Technical Report
  CMU-CyLab-09-011, June 2009.
  <http://www.cylab.cmu.edu/files/pdfs/tech_reports/CMUCyLab09011.pdf>

The implementation of Lockdown contained herein leverages
[XMHF](../xmhf). Note that the implementation is a ***research
prototype*** and does not yet fully provide the security properties of
the design.
