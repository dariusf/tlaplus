
This is a collection of experimental extensions to the TLA+ tools.
Some are described in the paper [Protocol Conformance with Choreographic PlusCal](https://dariusf.github.io/cpluscal.pdf).

# Project structure

benchmarks.t/run.t contains cpcal tests

Open IntelliJ in tlatools/org.lamport.tlatools

Entry points:

- cpcal: most of the changes are in src/pcal/PlusCalExtensions.java, extends PlusCal translator
- Monitoring: src/tlc2/TLC.java, extends normal TLC frontend
- MBTC: src/tlc2/mbtc/Rectify.java

# Development

Build

```sh
source build.sh
compile
```

Ad hoc testing

```sh
cd benchmarks.t
export tlaroot=..
source ../build.sh
tlc Chor.tla
```

Running tests

```sh
dune test
```

# Choreographic PlusCal

Run PlusCal translator as usual:

```sh
java -XX:+UseParallelGC -cp tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans benchmarks.t/Chor.tla
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

    It is started in benchmarks.t because raft.tla is there.

    The last raw trace from bisecting is written to benchmarks.t/trace.json.

    The counterexample is memoized to cex.json.

5. Localization

    Code is all in Rectify

6. Synthesis

