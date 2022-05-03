# Verified-FEC
Verification of Forward Erasure Correction in Coq

This is the CAV 2022 artifact for

Joshua M. Cohen, Qinshi Wang, and Andrew W. Appel. Verified
Erasure Correction in Coq with MathComp and VST, *34th International Conference
on Computer-Aided Verification (CAV)*, 2022.

## VM Instructions

1. Load the .ova file (cav22-ae.ova) into Virtualbox
2. Start the VM
3. Log in with the username and password "cav22-ae"
4. Start a terminal and navigate to `~/Desktop/Verified-FEC`
5. From here, you can run the commands to build the code, in
section "Building the Proofs" below


The rest of this file contains the information for the repository located
1. on the VM at ~/Desktop/Verified-FEC
2. at https://github.com/verified-network-toolchain/Verified-FEC/tree/cav22-ae


## Overview

Forward Erasure Correction is a technique of expanding k network packets
with h extra packets so that if some packets (no more than h) are lost,
the missing packets can be reconstructed without retransmission.
It uses a 1990 algorithm by Anthony McAuley of Bellcore, implemented in C
by McAuley and improved in 1997 by Vinh Lam for the Naval Research Lab.

## Dependencies

This repo builds under the Coq Platform 2022.04.0 (Coq 8.15.1). The individual
dependencies are:
1. Coq 8.15.1
2. Compcert 3.10
3. VST 2.9.1
4. Mathematical Components 1.14.0

It should run on any machine that has the latest Coq Platform installed, and has
been tested on Ubuntu 20.04 and Linux Mint 20.

## Building the Proofs

The proofs can be built either sequentially or in parallel.
`make -j 3` builds the proofs in parallel using 3 cores. This
reduces the amount of time needed (see "Resource Requirements" below).

`make` builds the proofs sequentially.

After all the proofs have been built, the last file outputs the axioms that
the main theorems depend on.

`make clean` will remove all built proofs, in case the process needs to be
restarted.

## Repository Structure

The repository is split into 3 parts:
1. The high-level functional model, which is written purely in MathComp/Coq
and contains the mathematical specification and proof of correctness of 
the underlying algorithm. This is independent of any implementation and does
not rely on C or VST.
2. The low-level functional model, which is written using types that can be
understood by CompCert/VST (ie: Z, list(list byte), etc). We include translations
and equivalence lemmas between the high and low-level models so that we can
show that the correctness theorem holds at the low level.
3. The VST proofs, which prove that the C program implements the low-level
functional model.

The specific files are as follows:

- src/fecActuator - C code and the corresponding Coq files generated
by Clightgen
- proofs/ - Coq proofs
	- Common/ - general helper lemmas and ways to relate basic MathComp
	functions with those of the Coq standard library and Compcert
	- Poly/ - proofs about polynomials
		- BoolField.v - the field of 2 elements
		- PolyField.v - results about finite fields constructed via irreducible
		and primitive polynomials
		- ByteField.v - the above results specialized for the field GF(256) 
		defined directly on bytes
		- ListPoly.v - computable polynomial division to calculate specific
		irreducible and primitive polynomials
	- Matrix/ - proofs about matrices
		- Gaussian.v - proofs about Gaussian elimination and properties of 
		row operations
		- GaussRestrict.v - Restricted Gaussian elimination
		- LinIndep.v - prove that matrices are invertible iff their rows are linearly independent
		- Vandermonde.v - definitions and properties of Vandermonde matrices
		- ListMatrix.v - Convert between MathComp matrices and explicit list(list F) indexed by Z (integers)
		- MatrixTransform.v - map over/flatten/unflatten matrices
		- VandermondeByte.v - definition and proof of specific Vandermonde/weight matrix used in C code
	- RS/ - proofs about Reed-Solomon
		- ReedSolomon.v - definitions and proofs about (high-level/MathComp) functional encoder and decoder,
		including proof of decoder correctness 
		- ReedSolomonList.v - convert these definitions to low-level functional model (via ListMatrix.v) and
		prove the low-level decoder correctness theorem
	- VST/ - proofs about C code
		- CommonVST.v - generic lemmas about data_at, pointer comparison/arithmetic, iter_sepcon
		- Specs.v - VST funspecs for C code
		- FECTactics.v - tactics for use in VST proofs
		- PopArrays.v - define generic pattern of iterating over/populating array and specific instances used
			in C encoder/decoder
		- Verif_field.v - VST proofs for field table generation
		- Verif_matrix.v - VST proofs for (Restricted) Gaussian elimination
		- Verif_encode.v - VST proofs for encoder
		- Verif_decode.v - VST proofs for decoder
	- Eval.v - show axioms used in major results

All VST-related proofs are in the VST folder.
The low-level functional model is found in Matrix/ListMatrix.v,
Matrix/MatrixTransform.v, Matrix/VandermondeByte.v, and RS/ReedSolomonList.v.
All other files are part of the high-level functional model.

## Main Definitions and Theorems

### Definitions

- `encoder` (RS/ReedSolomon.v, line 30) is the high-level functional encoder
(shown in Section 4.1 of the paper)

- `decoder` (RS/ReedSolomon.v, line 163) is the high-level functional decoder
(also shown in Section 4.1 of the paper)

- `encoder_list` (RS/ReedSolomonList.v, line 46) is the low-level functional encoder

- `decoder_list` (RS/ReedSolomonList.v, line 1235) is the low-level functional decoder
(though `decode_list_mx` on line 723 contains most of the decoder's logic)

- `fec_blk_encode_spec` (VST/Specs.v, line 140) is the VST spec for the C encoder function
(shown in Appendix F.5 of the paper)

- `fec_blk_decode_spec` (VST/Specs.v, line 169) is the VST spec for the C decoder function
(shown in Appendix F.6 of the paper)

### Theorems

- `decoder_correct` (RS/ReedSolomon.v, line 181) is the high-level decoder correctness theorem
(shown in Section 5.1 of the paper)

- `decoder_list_correct` (RS/ReedSolomonList.v, line 1258) is the low-level decoder correctness
theorem
(shown in Appendix F.2 of the paper)

- `body_fec_blk_encode` (VST/Verif_encode.v, line 28) is the proof that the C encoder satisfies
its VST spec

- `body_fec_blk_decode` (VST/Verif_decode.v, line 2103) is the proof that the C decoder
satisfies its VST spec

### Key Lemmas

- `any_submx_unitmx` (Matrix/Vandermonde.v, line 760) is the result that any square submatrix of
the weight matrix (the RHS of a row-reduced Vandermonde matrix on distinct elements) is invertible
(Theorem 1 in the paper)

- `vandermonde_unitmx` (Matrix/Vandermonde.v, line 168) is the classic result that a square Vandermonde 
matrix on distinct elements is invertible (Theorem 2 in the paper)

- `gaussian_elim_equiv` (Matrix/GaussRestrict.v, line 923) is the result that standard Gaussian
elimination and Restricted Gaussian Elimination are equivalent iff the matrix is strongly
invertible (Theorem 3 in the paper)

- `r_strong_inv_preserved` (Matrix/GaussRestrict.v, line 591) is the result that strong
invertibility is preserved across iterations of Restricted Gaussian Elimination
(Lemma 1 in the paper)

- `vandermonde_strong_inv` (Matrix/VandermondeByte.v, line 294) is the result that the
Vandermonde matrix used in this application is strongly invertible
(Theorem 4 in the paper)

- `any_submx_strong_inv` (Matrix/Vandermonde.v, line 824) is a corollary of `any_submx_unitmx`, 
proving that any square submatrix of the weight matrix is strongly invertible
(Theorem 5 in the paper)


## Design and Reusability

The high-level functional model is completely independent of the C implementation, and
is meant to serve as an independent, formal spec of the RSE algorithm. Beyond this, we have
structured our proofs in a way such that they are as reusable and general as possible.
We give some examples below:

- We included the theory of finite fields via polynomials quotiented by irreducible
or primitive polynomials (in Poly/PolyField.v) - this is generic in the choice of base field
and polynomial and thus provides a template to construct any finite field of size p^q, where
p is prime and q > 1. We only required one specific field (GF(256)) in our application; we are
in the process of submitting the finite field construction as a pull request to MathComp.

- We developed the theory of row-equivalence and Gaussian elimination in full generality
(Matrix/Gaussian.v), though we only deal with the Restricted case in the C code. This
presentation is intended to be close to textbook treatments of row reduction and is
expressed entirely in terms of MathComp types and operations.

- Our presentation of Vandermonde matrices and the RSE algorithm is intended to be
as general as possible. Our versions work over any (suitably large) field,
are generic in the choice of elements used to construct the Vandermonde matrix
(so long as the elements are distinct), and use full Gaussian elimination.
The RSE decoder also includes another version specialized to fields with
characteristic 2 to better match the C implementation; however, this is still
parameterized by the field and Vandermonde elements.

## Axioms

No additional axioms were used in this proof development, other than those
already included in CompCert/VST (MathComp does not use any axioms). Many of
these come from CompCert's definitions of the operational semantics of C, imported
by VST. All axioms involved are quite standard, and are known to be consistent
with each other. The expected axioms are shown in the `Eval.v` file.

## Resource Requirements

The included VM has 4 cores and 8 GB of RAM.
Building the proofs in parallel (with `make -j 3`) took just
under 10 minutes. Doing it sequentially (with `make`) took
just under 13 minutes (over half of this is for `Verif_decode.v`).

The underlying machine used was a Lenovo X1 Carbon 7th gen,
with a Intel Core i7-8565U CPU @ 1.80GHz processor and 16 GB of RAM.
We tested with a base OS of both Linux Mint 20 and Windows 10 on
this machine.

In general, the development needs about 5 GB of RAM to verify reliably,
but should be able to be built on any decently-powerful laptop.

## License and Funding

LICENSE: Peraton Labs (the successor company of Bellcore) open-sourced
the code in 2021 under the Apache 2.0 license, and Cohen and Appel
open-sourced the proof under the same license.  See [LICENSE.md](LICENSE.md)

FUNDING ACKNOWLEDGEMENT: DARPA funded the original development
of the algorithm and program (in the 1990s) and funded the
proof of correctness (in the 2020s).

