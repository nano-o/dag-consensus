# Optimistic, Signature-Free Reliable Broadcast and Its Applications: Formal Specifications

This directory contains formal specifications of protocols appearing the paper "Optimistic, Signature-Free Reliable Broadcast and Its Applications", CCS 2025. The specifications are written in the PlusCal/TLA+ language and their properities can be checked using the TLC model checker. The included Makefile allows running the model-checker.

WARNING: If you run the model-checker, it will by default try to reserve 16GB of memory and will use 8 CPU cores. If this is too much (or too little) for your system, edit the variables `TLC_OFFHEAP_MEMORY`, `TLC_HEAP`, and `TLC_WORKERS` in the `Makefile`.

## Specification of Sailfish++

The specification appears in `Sailfish.tla`.

To check the specification with the TLC model-checker:
* The specification uses PlusCal, which must be transpiled to TLA+ first. To perform the translation, run `make trans TLA_SPEC=Sailfish.tla` (this will modify `Sailfish.tla` in place).
* Then you can run the TLC model-checker with `make run-tlc TLA_SPEC=TLCSailfish1.tla`. `TLCSailfish1.tla` imports `Sailfish.tla` and provides concrete definitions for model-checking, and `TLCSailfish1.cfg` specifies what to check.

Note that the run-time of the model-checker should be fairly short. This is because we abstract over many aspects of the protocol (e.g. reliable-broadcast). On a recent desktop machine, it takes about 30 seconds and explores 953,442 distinct states.

## Specification of the two-step optimistic broadcast protocol

The specification appears in `TwoStepOptimiticBroadcast.tla`.

Unfortunately, the state-space of this specification is too large for practical model-checking.
Instead, we provide `TwoStepOptimiticBroadcastSafety.tla`, which abstracts over the messages that Byzantine parties send in order to reduce the state-space. This abstraction is however only sound for safety checking, not liveness checking.

To check `TwoStepOptimiticBroadcastSafety.tla` with the TLC model-checker:
* First, run `make trans TLA_SPEC=TwoStepOptimiticBroadcastSafety.tla` to transpile the PlusCal part of the specification to TLA+.
* Second, run `make run-tlc TLA_SPEC=TwoStepOptimiticBroadcastSafety.tla`. This will run the TLC model-checker according to the configuration found in `TwoStepOptimiticBroadcastSafety.cfg`. By default, it will exhaustively check the safety of the protocol for two possible broadcast values and 6 parties among which the broadcaster party is malicious; it will also by default use symmetry reduction to further reduce the state-space. This takes about 50 minutes on a recent desktop computer and explores 1,161,459 distinct states.
