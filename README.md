# TLA+/PlusCal specifications of DAG-based consensus protocols

The specifications use PlusCal, which must be transpiled to TLA+.
For this, run e.g. `make trans TLA_SPEC=Sailfish.tla`.
Then you can run the TLC model-checker with e.g. `make run-tlc TLA_SPEC=TLCSailfish1.tla`.
The corresponding TLC configuration file is in `TLCSailfish1.cfg`
You might want to adjust the memory that TLC tries to allocate and the number of processors to use; it's all in the Makefile.

For `TwoStepOptimiticBroadcast.tla`: run `make trans TLA_SPEC=TwoStepOptimiticBroadcast.tla` and then, to run TLC, `make run-tlc TLA_SPEC=TwoStepOptimiticBroadcast.tla`

You can also typeset a specification with e.g. `make Sailfish.pdf`.
