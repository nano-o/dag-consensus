# TLA+/PlusCal specifications of DAG-based consensus protocols

The specifications use PlusCal, which must be transpiled to TLA+.
For this, run e.g. `make trans Sailfish1.tla`.
Then you can run the TLC model-checker with e.g. `make run-tlc Sailfish1.tla`.
The corresponding configuration of TLC is in `Sailfish1.cfg`

Note that we apply aggressive "sequentialization" in order to speed up model-checking (see `SeqSpec` in e.g. `Sailfish1.tla`)
