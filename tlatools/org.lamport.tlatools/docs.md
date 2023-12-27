
This is a collection of experimental extensions to the TLA+ tools.
Some are described in the paper [Protocol Conformance with Choreographic PlusCal](https://dariusf.github.io/cpluscal.pdf).

- [Project structure](#project-structure)
- [Development](#development)
- [Choreographic PlusCal](#choreographic-pluscal)
- [MBTC flow](#mbtc-flow)

# Project structure

cpcal.t/run.t contains Choreographic PlusCal tests

mbtc.t/run.t contains MBTC inputs

IntelliJ project is in tlatools/org.lamport.tlatools

Entry points:

- Choreographic PlusCal: extends PlusCal translator pcal.trans, most of the changes are in src/pcal/PlusCalExtensions.java, start at src/pcal/ParseAlgorithm.java, GetChoreography
- Monitoring: src/tlc2/TLC.java, extends normal TLC frontend
- MBTC: src/tlc2/mbtc/RunMBTC.java

# Development

Build tla2tools.jar

```sh
source build.sh
compile
# tlatools/org.lamport.tlatools/dist/tla2tools.jar
```

Running tests

```sh
dune test
```

# Choreographic PlusCal

Ad hoc testing

```sh
cd cpcal.t
export tlaroot=..
source ../build.sh
pluscal Chor.tla
```

# MBTC flow

1. Start implementation

    ~/refinement-mappings/projects/etcd-raft is the library with instrumentation, ~/refinement-mappings/projects/etcd/contrib/raftexample is the executable.

    ```sh
    cd raftexample
    ./run.sh
    ```

2. Generate tests

    ```sh
    cd trace-specs
    FULL=1 python .
    ```

    Each node `n` writes to log-`n`.ndjson, and writes its stdout to node`n`.log.

3. Collate logs

    ```sh
    LOG=1 python .
    ```
    This produces log.json in raftexample, which contains the concrete implementation trace.

4. MBTC

    MBTC.run reads log.json from raftexample and invokes TLC repeatedly to bisect the trace and find a counterexample.

    It is started in mbtc.t because raft.tla is there.

    The last raw trace from bisecting is written to mbtc.t/trace.json.

    The counterexample is memoized to cex.json.

5. Localization

    Code is all in Rectify

6. Synthesis

