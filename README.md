# Optimistic, Signature-Free Reliable Broadcast and Its Applications: Formal Specifications

This directory contains formal specifications of protocols appearing the paper "Optimistic, Signature-Free Reliable Broadcast and Its Applications", CCS 2025. The specifications are written in the PlusCal/TLA+ language and their properities can be checked using the TLC model checker. The included Makefile allows running the model-checker.

WARNING: If you run the model-checker, it will by default try to reserve 16GB of memory and will use 8 CPU cores. If this is too much (or too little) for your system, edit the variables `TLC_OFFHEAP_MEMORY`, `TLC_HEAP`, and `TLC_WORKERS` in the `Makefile`.

## Specification of Sailfish++

The specification appears in `Sailfish.tla`.

To check the specification with the TLC model-checker:
* The specification uses PlusCal, which must be transpiled to TLA+ first. To perform the translation, run `make trans TLA_SPEC=Sailfish.tla` (this will modify `Sailfish.tla` in place).
* Then you can run the TLC model-checker with `make run-tlc TLA_SPEC=TLCSailfish1.tla`. `TLCSailfish1.tla` imports `Sailfish.tla` and provides concrete definitions for model-checking, and `TLCSailfish1.cfg` specifies what to check.

Note that the run-time of the model-checker should be fairly short. This is because we abstract over many aspects of the protocol (e.g. reliable-broadcast).

## Specification of the two-step optimistic broadcast protocol

The specification appears in `TwoStepOptimiticBroadcast.tla`.

To check the specification with the TLC model-checker:
* First, run `make trans TLA_SPEC=TwoStepOptimiticBroadcast.tla` to transpile the PlusCal part of the specification to TLA+.
* Second, run `make run-tlc TLA_SPEC=TwoStepOptimiticBroadcast.tla`. This will run the TLC model-checker according to the configuration found in `TwoStepOptimiticBroadcast.cfg`. By default, it will exhaustively check the safety of the protocol for two possible broadcast values and 4 parties among which the broadcaster party is malicious; symmetry reduction is also used to reduce the state-space. This takes about TODO minutes on a recent desktop computer and explores X number of states.
* To check liveness, uncomment `PROPERTY Liveness` in `TwoStepOptimiticBroadcast.cfg` and comment out `SYMMETRY Symm` (symmetry reduction is not supported for liveness checking). Then run `make run-tlc TLA_SPEC=TwoStepOptimiticBroadcast.tla`. Note that, since symmetry reduction is disabled, this will take significantly longer.

Note that `TwoStepOptimiticBroadcast.cfg` contains other, larger configurations (which are commented out).
Unfortunately, exhaustive checking of those larger configurations seems unrealistic as their state-space is very large (the machine on which we tried ran out of disk space to store the state-space).
