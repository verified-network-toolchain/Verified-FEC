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

In 2021 the core of the algorithm was proved correct (after correcting a latent undefined behavior bug) by Josh
Cohen at Princeton University, advised by Andrew Appel 
and with assistance from Qinshi Wang[^1].

[^1]: Joshua M. Cohen, Qinshi Wang, and Andrew W. Appel. Verified
Erasure Correction in Coq with MathComp and VST, *34th International Conference
on Computer-Aided Verification (CAV)*, 2022.

Verification of other parts of the program (packet handling
and buffer manager for sender and for receiver) are described in the paper
"Specifying and Verifying a Real-World Packet Error-Correction System".
The proofs accompanying this paper can be found in the directory 
[proofs/FEC](proofs/FEC) and the code can be found in [src/*/mini_prod3](src/).

Dependencies: This repo requires Coq 8.18, VST 2.13, and Mathematical Components 2.1, and
Coq Record Update 3.3.0.
It builds with the November 2023 Coq Platform (& coq-record-update).

LICENSE: Peraton Labs (the successor company of Bellcore) open-sourced
the code in 2021 under the Apache 2.0 license, and Cohen and Appel
open-sourced the proof under the same license.  See [LICENSE.md](LICENSE.md)

FUNDING ACKNOWLEDGEMENT: DARPA funded the original development
of the algorithm and program (in the 1990s) and funded the
proof of correctness (in the 2020s).

