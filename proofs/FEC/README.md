# End-to-End Proofs

This folder contains the proof scripts accompanying the paper "Specifying and Verifying a Real-World Packet Error-Correction System" by Joshua M. Cohen and Andrew W. Appel.
See the [src](../src) folder for information about the underlying C code (both original and modified).

## Compilation

This repo builds under Coq 8.16.1 and depends on MathComp 1.15.0, coq-record-update 0.3.0, and VST 2.11.1. All of these dependencies are part of the Coq Platform, November 2022 release.
To build all of the proof scripts, navigate to the repo root directory and run `make`. The `Verif_*.v` files are the VST proofs for the core algorithm implementation; they take longer to
build but are not needed for the end-to-end proofs discussed in the paper.

## Repo Structure

This folder contains the following files:
- `AssocList.v` - Association lists with unique keys
- `AbstractPacket.v` - Abstract notion of packet with header
- `Endian.v` - 4- and 16-bit integers, endianness and converting between host and network byte order, convert words to bytes and back
- `IP.v` - IP and UDP data types with headers and length invariants, recover packet structure from byte sequence
- `CommonFEC.v` - generic results about list operations, nats, absolute value, sublists, and others
- `Block.v` - definition of FEC (concrete) packets, Block data structure, predicates on Blocks, convert packet stream to Block stream, subblocks
- `Producer.v` - definition of FEC producer and theorems about its output
- `ConsumerGeneric.v` - generic version of FEC consumer (parametric in choice of timeout mechanism), results about Reed-Solomon decoder on Block, relating Producer and Consumer
- `ConsumerNoTimeouts.v` - FEC Consumer with no timeouts, prove that packets are recovered with bounded loss
- `Reorder.v` - Definition of RD (Reorder Density), theorems about reordering and duplication
- `ConsumerTimeouts.v` - FEC Consumer with timeouts (but unbounded integers), show that reorder+duplication bounds give same output as non-timeout version
- `SeqCmp` - Serial number arithmetic for arbitrary machine-length integers
- `ConsumerMachine.v` - FEC Consumer with machine-length integers and serial number arithmetic
- `ProducerConsumerCorrectness.v` - Full specs and theorems about Producer and Consumer

## Key Definitions and Theorems

### Section 5.2

- Proof of Property 2 - `all_data_sent` in `ProducerConsumerCorrectness.v`
- Proof of Property 3 - `all_decoded_in` in `ProducerConsumerCorrectness.v`
- Condition 1 - `loss_cond_i` in `ProducerConsumerCorrectness.v`

### Section 6

- RD definition - `ri` and `displ` in `Reorder.v`

### Section 8.1

- Block definition - `Block` in `Block.v`
- Producer definition - `producer_all_steps` in `Producer.v`

### Section 8.3

- Consumer definition with no timeouts - `consumer_all_steps_nto` in `ConsumerNoTimeouts.v`
- Consumer definition with timeouts - `consumer_all_steps` in `ConsumerTimeouts.v`
- Consumer definition with machine-length ints - `consumer_all_steps_m` in `ConsumerMachine.v`
- Model 1 recovers all packets - `all_packets_in_block_recovered` in `ConsumerNoTimeouts.v`
- Theorem 1 - `u_seqNum_reorder_bound` in `Reorder.v`
- Theorem 2 - `packets_reorder_dup_bound` in `Reorder.v`
- Models 1 and 2 equivalent - `consumer_timeout_notimeout_all` in `ConsumerTimeouts.v`
- Theorem 3 - `seq_lt_lt` in `SeqCmp.v`
- Models 2 and 3 equivalent - `consumer_all_steps_m_eq` in `ConsumerMachine.v`
- Theorem 4 - `block_i_recovered` in `ProducerConsumerCorrectness.v`
- Corollary 1 - `orig_decoded_streams` in `ProducerConsumerCorrectness.v`
