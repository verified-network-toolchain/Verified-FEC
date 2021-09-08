# Verified-FEC
Verification of Forward Erasure Correction in Coq

Forward Erasure Correction is a technique of expanding k network packets
with h extra packets so that if some packets (no more than h) are lost,
the missing packets can be reconstructed without retransmission.
It uses a 1990 algorithm by Anthony McAuley of Bellcore, implemented in C
by McAuley and improved in 1997 by Vinh Lam for the Naval Research Lab.

The algorithm was patented (#5,115,436) in 1992.  We believe the
patent expired on May 4, 2020 -- but that's not a warranty, get your
own lawyer.

In 2021 the core of the algorithm was proved correct* by Josh
Cohen at Princeton University, advised by Andrew Appel 
and with assistance from Qinshi Wang.
*except for a latent undefined behavior bug; see the forthcoming
technical report.

Verification of other parts of the program (packet handling
and buffer manager for sender and for receiver) are ongoing work.

LICENSE: Peraton Labs (the successor company of Bellcore) open-sourced
the code in 2021 under the Apache 2.0 license, and Cohen and Appel
open-sourced the proof under the same license.  See [LICENSE.md](LICENSE.md)

FUNDING ACKNOWLEDGEMENT: DARPA funded the original development
of the algorithm and program (in the 1990s) and funded the
proof of correctness (in the 2020s).

