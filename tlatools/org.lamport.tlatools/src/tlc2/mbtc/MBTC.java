package tlc2.mbtc;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.reflect.TypeToken;
import gov.nasa.jpf.util.Pair;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefOrDeclNode;
import tlc2.TLCRunner;
import tlc2.monitor.Monitoring;
import tlc2.synth.Eval;
import tlc2.tool.impl.FastTool;
import tlc2.value.IValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;

import java.io.*;
import java.lang.reflect.Type;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

public class MBTC {

    private static final Type LIST_EVENT = new TypeToken<ArrayList<Event>>() {
    }.getType();
    private static final Type LIST_STATE = new TypeToken<ArrayList<State>>() {
    }.getType();

    public static Gson gson = new GsonBuilder()
            .registerTypeAdapter(Value.class, new ValueAdapter())
            .registerTypeAdapter(State.class, new State.Adapter())
            .create();

    private static final boolean DEBUG = true;

    public void log(String s, Object... stuff) {
        if (!DEBUG) {
            return;
        }
        System.out.printf(s + "\n", stuff);
    }

    public Optional<Cex> run() throws IOException {

//        String spec = new File("../../benchmarks.t/raft.tla").getAbsolutePath();
//        String spec = "/Users/darius/java/tlaplus/benchmarks.t/raft.tla";
        String spec = "raft";
        String config = spec;

        FastTool tool = new FastTool(spec, config);
        boolean allowStuttering = false;
        String originalSpec = "raft";
        Path specDir = Paths.get(".").toAbsolutePath();

        Reader reader = Files.newBufferedReader(Paths.get("/Users/darius/refinement-mappings/projects/etcd/contrib/raftexample/log.json"));
        List<Event> implTrace = gson.fromJson(reader, LIST_EVENT);

        Function<Integer, Optional<List<State>>> align = i -> {
            if (i == null) {
                log("checking for full alignment");
            } else {
                log("trying to find alignment at %d", i);
            }
            return checkAlignment(tool, specDir, implTrace, i, allowStuttering, originalSpec);
        };

        Optional<List<State>> initialAlignment = align.apply(null);
        if (initialAlignment.isPresent()) {
            log("OK!");
            return Optional.empty();
        }
        log("cannot align full trace, bisecting to find counterexample");
        Optional<Cex> cex = bisectAlignment(implTrace.size() - 1, align);

        return cex.map(c -> {
            c.frontier = findFrontier(tool, specDir, originalSpec, c.tracePrefix.get(c.tracePrefix.size() - 1));
            c.implTrace = implTrace;
            return c;
        });
    }

    Optional<Cex> bisectAlignment(int index, Function<Integer, Optional<List<State>>> align) {
        Pair<Integer, Optional<List<State>>> res = binarySearchRightmost(1, index, align, m -> {
            if (m.isEmpty()) {
                log("failed, trying shorter");
            } else {
                log("succeeded, trying longer");
            }
            return m.isEmpty();
        });

        log("bad state at index " + res._1);

        return res._2.map(r -> {
            Cex cex = new Cex();
            cex.prefixI = res._1;
            cex.tracePrefix = r;
            return cex;
        });
    }

    /**
     * Finding the point of divergence:
     * 1 1 1 2 3 4
     * ....^
     * <a href="https://en.wikipedia.org/wiki/Binary_search_algorithm#Procedure_for_finding_the_rightmost_element">...</a>
     * assuming 1 represents a trace with an invariant violation witnessing refinement
     */
    public static <T> Pair<Integer, T> binarySearchRightmost(int l, int r,
                                                             Function<Integer, T> test,
                                                             Predicate<T> is_left) {
        T data = null;
        while (l < r) {
            int mid = l + (r - l) / 2;
            T d = test.apply(mid);
            if (is_left.test(d)) {
                r = mid;
            } else {
                data = d;
                l = mid + 1;
            }
        }
        return new Pair<>(r - 1, data);
    }


    private Optional<List<State>> checkAlignment(FastTool tool, Path specDir,
                                                 List<Event> implTrace, Integer i,
                                                 boolean allowStuttering, String originalSpec) {

        try {
            Path dir = buildAuxSpecs(tool, implTrace, i, allowStuttering, originalSpec);
            String constants = getConstantsConfig(tool);

            String config = String.format("%s\n" +
                    "INVARIANT Check\n" +
                    "INIT Init\n" +
                    "NEXT Next\n" +
                    "CHECK_DEADLOCK FALSE", constants);

            Files.writeString(dir.resolve("MTrace4.cfg"), config);
            copyFiles(".tla", specDir, dir);

            TLCRunner runner = new TLCRunner(
                    List.of("-noGenerateSpecTE", "-cleanup", "-dumpTrace", "json", "trace.json", "MTrace4.tla"),
//                new File("../../benchmarks.t").getAbsoluteFile(),
                    dir,
                    dir.resolve("tlc.log").toFile());
            runner.setSilenceStdOut(true);
            runner.run();

            Path traceFile = dir.resolve("trace.json");
            if (traceFile.toFile().exists()) {
                Reader reader = Files.newBufferedReader(traceFile);
                List<State> trace = gson.fromJson(reader, LIST_STATE);
                return Optional.of(trace);
            } else {
                return Optional.empty();
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public List<State> findFrontier(FastTool tool, Path specDir, String originalSpec, State init) {
        try {
            final Path dir = Files.createTempDirectory("frontier");
            Path specPath = dir.resolve(originalSpec + ".tla");
            {
                String constants = getConstantsConfig(tool);
                String config = String.format("%s\n" +
                        "CONSTRAINT FrontierConstr\n" +
                        "INIT FrontierInit\n" +
                        "NEXT Next\n" +
                        "CHECK_DEADLOCK FALSE", constants);
                Files.writeString(dir.resolve(originalSpec + ".cfg"), config);
                copyFiles(".tla", specDir, dir);
            }

            String modifiedSpec = Files.readString(specPath);
            {
                Set<String> mbtcBlacklist = Set.of("i");
                String constrDef = "FrontierConstr == TLCGet(\"level\") <= 2";
                String initDef = "FrontierInit == " +
                        init.data.entrySet().stream()
                                .filter(e -> !mbtcBlacklist.contains(e.getKey()))
                                .map(e -> String.format("%s = %s", e.getKey(), Eval.prettyPrint(e.getValue())))
                                .collect(Collectors.joining(" /\\\\ "));
                modifiedSpec = modifiedSpec.replaceAll("={5,}",
                        String.join("\n\n", List.of(constrDef, initDef, "$0")));
                Files.writeString(specPath, modifiedSpec,
                        StandardOpenOption.TRUNCATE_EXISTING);
            }

            TLCRunner runner = new TLCRunner(
                    List.of("-noGenerateSpecTE", "-cleanup", "-dump", "json", "dump.json", originalSpec + ".tla"),
                    dir,
                    dir.resolve("tlc.log").toFile());
            runner.setSilenceStdOut(true);
            runner.run();

            Path dumpFile = dir.resolve("dump.json");
            Reader reader = Files.newBufferedReader(dumpFile);

            List<State> states = Objects.requireNonNull(gson.fromJson(reader, LIST_STATE));

            // ignore stuttering states in the frontier
            states = states.stream()
                    .filter(s -> s.data.get("actions").size() > 0)
                    .collect(Collectors.toList());
            return states;

        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static String getConstantsConfig(FastTool tool) {
        Map<OpDefOrDeclNode, Object> defs =
                tool.getSpecProcessor().getConstantDefns().get(tool.getSpecProcessor().getRootModule());
        return Arrays.stream(tool.getSpecProcessor().getRootModule().getConstantDecls())
                .map(o -> String.format("CONSTANT %s = %s", o.getName().toString(),
                        Eval.prettyPrint((IValue) defs.get(o))))
                .collect(Collectors.joining("\n"));
    }

    private Path buildAuxSpecs(FastTool tool, List<Event> trace, Integer length,
                               boolean allowStuttering, String originalSpec) {

        try {
//        final Set<String> metaFields = Set.of("who", "actions");
//            final Set<String> metaFields = Set.of();
            final Path tempDir = Files.createTempDirectory("mbtc");

            String file3 = Objects.requireNonNull(Monitoring.getResourceFileAsString("tlc2/mbtc/MTrace3.tla.template"));
            String file4 = Objects.requireNonNull(Monitoring.getResourceFileAsString("tlc2/mbtc/MTrace4.tla.template"));

            ModuleNode rootModule = tool.getSpecProcessor().getSpecObj().getRootModule();
            Set<String> allVariables = Arrays.stream(rootModule.getVariableDecls())
                    .map(o -> o.getName().toString())
//                .filter(v -> !metaFields.contains(v))
                    .collect(Collectors.toSet());

            Set<String> traceAssignedVariables = trace.get(0).data.keySet();

            String mtrace3;
            {
                String trace1 = IntStream.range(0, trace.size()).mapToObj(i -> {
                    Event ev = trace.get(i);
                    FcnRcdValue traceEv = new FcnRcdValue(
                            ev.data.entrySet().stream().collect(Collectors.toMap(e ->
                                    new StringValue(e.getKey()), e -> e.getValue())),
                            true);
                    FcnRcdValue item = new FcnRcdValue(Map.of(
                            new StringValue("who"), new StringValue(ev.who),
                            new StringValue("data"), traceEv), true);
                    String desc = String.format("\\* %d | %s | %s", i + 1, ev.clock, ev.label);
                    return String.format("  %s\n  %s%s", desc, i > 0 ? ", " : "", Eval.prettyPrint(item));
                }).collect(Collectors.joining("\n"));

                String traceAssignments = traceAssignedVariables.stream()
                        .map(v -> String.format("/\\ %s[Tr[i].who] = Tr[i].data[\"%s\"]", v, v))
                        .map(s -> "  " + s)
                        .collect(Collectors.joining("\n"));

                String traceAssignmentsPrimed = traceAssignedVariables.stream()
                        .map(v -> String.format("/\\ %s'[Tr[i'].who] = Tr[i'].data[\"%s\"]", v, v))
                        .map(s -> "  " + s)
                        .collect(Collectors.joining("\n"));

                String assignedStr = String.join(", ", traceAssignedVariables);
                mtrace3 = String.format(file3,
                        trace1, assignedStr, assignedStr,
                        traceAssignments, traceAssignmentsPrimed);
            }

            String mtrace4;
            {
                Set<String> otherVariables = new HashSet<>(allVariables);
                otherVariables.removeAll(traceAssignedVariables);

                Set<String> constants = Arrays.stream(tool.getSpecProcessor().getRootModule().getConstantDecls())
                        .map(o -> o.getName().toString())
                        .collect(Collectors.toSet());

                String orStutter = Stream.of(
                                "\\/ UNCHANGED varsA /\\ NextB \\* unchanged must come first (TLC)",
                                "\\/ UNCHANGED varsB /\\ NextA")
                        .map(s -> allowStuttering ? s : "\\* " + s)
                        .map(s -> "  " + s)
                        .collect(Collectors.joining("\n"));
                String traceLength = length == null ? "Len(Tr)" : ("" + length);
                String varDecls = otherVariables.isEmpty() ? ""
                        : ("VARIABLES " + String.join(", ", otherVariables));
                String constantDecls = constants.isEmpty() ? ""
                        : ("CONSTANTS " + String.join(", ", constants));

                String allVarsStr = String.join(", ", allVariables);

                mtrace4 = String.format(file4,
                        originalSpec, orStutter, originalSpec, varDecls, constantDecls,
                        allVarsStr, originalSpec, "Init", "Next", traceLength);
            }

            Files.writeString(tempDir.resolve("MTrace3.tla"), mtrace3);
            Files.writeString(tempDir.resolve("MTrace4.tla"), mtrace4);

            return tempDir;
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static void copyFiles(String suffix, Path specDir, Path dir) throws IOException {
        Files.walkFileTree(specDir, new FileVisitor<>() {
            @Override
            public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) {
                return FileVisitResult.CONTINUE;
            }

            @Override
            public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
                if (file.toString().endsWith(suffix)) {
                    Files.copy(file, dir.resolve(file.getFileName()));
                }
                return FileVisitResult.CONTINUE;
            }

            @Override
            public FileVisitResult visitFileFailed(Path file, IOException exc) {
                return FileVisitResult.CONTINUE;
            }

            @Override
            public FileVisitResult postVisitDirectory(Path dir, IOException exc) {
                return FileVisitResult.CONTINUE;
            }
        });
    }

    public static void main(String[] args) throws IOException {

        Cex cex;
        boolean memo = true;
//        boolean memo = false;
        if (memo) {
            cex = readCounterexample("cex.json");
        } else {
            Optional<Cex> res;
            res = new MBTC().run();
            ensure(res.isPresent());
            cex = res.get();
            writeCounterexample(cex);
        }

        Present.showCounterexample(cex);
    }

    private static Cex readCounterexample(String path) throws IOException {
        try (Reader reader = new FileReader(path)) {
            return Objects.requireNonNull(gson.fromJson(reader, Cex.class));
        }
    }

    private static void writeCounterexample(Cex cex) throws IOException {
        try (Writer writer = new FileWriter("cex.json")) {
            gson.toJson(cex, writer);
        }
    }

    public static void ensure(boolean cond) {
        if (!cond) {
            throw new IllegalStateException();
        }
    }
}
