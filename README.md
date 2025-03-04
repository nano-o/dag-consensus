# TLA+/PlusCal specifications of DAG-based consensus protocols

The specifications use PlusCal, which must be transpiled to TLA+.
For this, run e.g. `make trans SailFish.tla`.
Then you can run the TLC model-checker with e.g. `make run-tlc SailFish.tla`.
The corresponding configuration of TLC is in `SailFish.cfg`
