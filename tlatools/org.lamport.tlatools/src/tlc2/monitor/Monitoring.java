package tlc2.monitor;

import tla2sany.semantic.*;
import tlc2.tool.Defns;
import tlc2.value.IValue;
import tlc2.value.impl.*;
import util.UniqueString;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.BiFunction;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static tla2sany.semantic.ASTConstants.*;
import static tlc2.monitor.Translate.fail;

public class Monitoring {

//    static class MAction {
//        List<SemanticNode> pre;
//        List<SemanticNode> effects;
//
//        public MAction(List<SemanticNode> pre, List<SemanticNode> effects) {
//            this.pre = pre;
//            this.effects = effects;
//        }
//    }

    static String getResourceFileAsString(String fileName) throws IOException {
        ClassLoader classLoader = ClassLoader.getSystemClassLoader();
//        ClassLoader classLoader = Monitoring.class.getClassLoader();
        try (InputStream is = classLoader.getResourceAsStream(fileName)) {
            if (is == null) return null;
            try (InputStreamReader isr = new InputStreamReader(is);
                 BufferedReader reader = new BufferedReader(isr)) {
                return reader.lines().collect(Collectors.joining(System.lineSeparator()));
            }
        }
    }

    public static void convert(Defns defns, Map<UniqueString, IValue> initialState, ModuleNode rootModule) throws Exception {

        String overallTemplate = Objects.requireNonNull(getResourceFileAsString("tlc2/MonitorTemplate.go"));

        UniqueString moduleName = rootModule.getName();
        List<OpDeclNode> variables = Arrays.asList(rootModule.getVariableDecls());

        List<OpDefNode> definitions = rootModule.getDefinitions().stream()
                .filter(Monitoring::operatorWhitelist)
                .map(d -> (OpDefNode) d)
                .collect(Collectors.toList());

        String monitorFns = definitions.stream().flatMap(d -> {
            if (d.getBody() instanceof SubstInNode) {
                // INSTANCE declarations are one instance of this
                return Stream.of();
            }
            if (!(d.getBody() instanceof OpApplNode)) {
                throw fail("not op appl node?");
            }
            String params = translateParams(d, (i, p) -> String.format("%s any", p.getName().toString()));
            GoTranslation translation = new GoTranslation(defns);
            GoBlock body = translation.translateTopLevel(defns, d.getBody());
            String a = String.format("// Check%s\nfunc (m *Monitor) Check%s(%strace_i int, prev Event, this Event) error {\n%s\nreturn nil\n}",
                    d.getName(),
                    d.getName(),
                    params,
                    body
            );
            return Stream.of(a);
        }).collect(Collectors.joining("\n\n"));

        String pkg = "monitoring";
        String varDecls = variables.stream().map(v -> String.format("%s any", v.getName())).collect(Collectors.joining("\n"));

        String actionNames = definitions.stream()
                .map(d -> d.getName().toString())
                .collect(Collectors.joining("\n"));

        String stringSwitchCases =
                definitions.stream()
                        .map(d -> String.format("case %1$s:\nreturn \"%1$s\"", d.getName().toString()))
                        .collect(Collectors.joining("\n"));

        String checkSwitchCases =
                definitions.stream()
                        .map(d -> String.format("case %1$s:\nif err := m.Check%1$s(%2$si, prev, this); err != nil {\nreturn err\n}",
                                d.getName().toString(),
                                translateParams(d, (i, p) -> String.format("this.params[%d]", i)))
                        )
                        .collect(Collectors.joining("\n"));

        String imports = Stream.of("reflect", "fmt", "path", "runtime", "strings").map(s -> "\"" + s + "\"")
                .collect(Collectors.joining("\n"));

        String module = String.format(overallTemplate,
                pkg, imports, varDecls, actionNames,
                stringSwitchCases, checkSwitchCases, monitorFns);
//        String module = monitorFns;

        Path filename = Paths.get(moduleName + ".go");
        try {
            Files.write(filename, module.getBytes());
            System.out.println(filename.toAbsolutePath());
        } catch (IOException e) {
            // this is the case in dune due to sandboxing
            System.out.println("// MONITOR START");
            System.out.println(module);
            System.out.println("// MONITOR END");
        }
//        }

//        System.out.println(filename.toAbsolutePath());
//        System.out.println(Files.isWritable(filename));

//        File file = new File(moduleName + "1.go");
//        System.out.println(file.getAbsolutePath());
//        try (BufferedWriter writer = new BufferedWriter(new FileWriter(file))) {
//            writer.write(module);
//        } catch (IOException e) {
//            System.out.println(e.getMessage());
//            System.out.println(e.getCause().getMessage());
//            throw new RuntimeException(e);
//        }
//        System.out.println(file);
    }

    private static String translateParams(OpDefNode d, BiFunction<Integer, FormalParamNode, String> f) {
        String params;
        if (d.getArity() == 0) {
            params = "";
        } else {
            params =
                    IntStream.range(0, d.getArity())
                            .mapToObj(i -> f.apply(i, d.getParams()[i]))
                            .collect(Collectors.joining(", ")) + ", ";
        }
        return params;
    }

    private static boolean operatorWhitelist(SemanticNode d) {
        if (d instanceof OpDefNode) {
            String name = ((OpDefNode) d).getName().toString();
            List<String> extra = List.of("TC", "TCConsistent", "SoupSize", "TargetLength", "TargetA", "ConstrB", "TargetCommit", "TargetAbort");
            if (name.contains("TypeOK") || name.contains("Spec") || name.contains("vars") ||
                    name.contains("Next") || name.contains("Init")) {
                // Init is ignored because it's already availale.
                // we should get the actions from Next but we just keep everything left instead.
                return false;
            } else if (extra.contains(name)) {
                // User-defined blacklist
                return false;
            } else if (List.of("Messages", "Receive", "Send", "ToSet", "Option", "Some", "None").contains(name)) {
                // Library functions
                return false;
            } else if (List.of("Terminating", "Termination").contains(name)) {
                // generated by the PlusCal translator
                return false;
            }
            return true;
        } else {
            throw fail("not an op def node?");
        }
    }

//    private static boolean isNotPrimed(SemanticNode body) {
//        if (isConstant(body)) {
//            return true;
//        } else if (body instanceof OpApplNode) {
//            if (isPrimedVar(body)) {
//                return false;
//            }
//            return operatorArgs(body).stream().allMatch(Monitoring::isNotPrimed);
//        }
//        return true;
//    }
    /**
     * splits an operator body (represented as a $ConjList) into a list of preconditions and effects
     */
//    private static MAction splitPreEff(SemanticNode body) {
//        if (!(body instanceof OpApplNode)) {
//            throw fail("not op app node?");
//        }
//        UniqueString name = ((OpApplNode) body).getOperator().getName();
//        List<ExprOrOpArgNode> args = operatorArgs((OpApplNode) body);
//        if (name.equals("$ConjList")) {
//            List<SemanticNode> pre = new ArrayList<>();
//            List<SemanticNode> effects = new ArrayList<>();
//            args.stream().map(Monitoring::splitPreEff).forEach(m -> {
//                pre.addAll(m.pre);
//                effects.addAll(m.effects);
//            });
//            return new MAction(pre, effects);
//        }
//        boolean unprimed = args.stream().allMatch(Monitoring::isNotPrimed);
//        // check if it involves primed variables
//        if (unprimed) {
//            return new MAction(List.of(body), List.of());
//        } else {
//            return new MAction(List.of(), List.of(body));
//        }
//    }






//    private static GoExpr goExprDef(String def, String ) {
//        GoExpr res = new GoExpr();
//        res.defs.add(def);
//        res.expr = expr;
//        return res;
//    }

    /**
     * this produces an expression, but without defs
     */
    private static String translateIValue(IValue v) {
        if (v instanceof StringValue) {
            return "\"" + ((StringValue) v).getVal() + "\"";
        } else if (v instanceof IntValue) {
            return v.toString();
        } else if (v instanceof SetEnumValue) {
            // empty set
            return "map[any]bool{}";
        } else if (v instanceof TupleValue) {
            // empty seq
            return "[]any{}";
        } else if (v instanceof FcnRcdValue) {
            // record literals, like [r1 |-> "working"]
            List<String> res = new ArrayList<>();
            for (int i = 0; i < ((FcnRcdValue) v).domain.length; i++) {
                res.add(String.format("%s: %s",
                        translateIValue(((FcnRcdValue) v).domain[i]),
                        translateIValue(((FcnRcdValue) v).values[i])));
            }
            return String.format("map[any]any{%s}", res.stream().collect(Collectors.joining(", ")));
        }
        throw fail("invalid type of value " + v.getClass().getSimpleName());
    }

//    // visitors are for applying a transformation uniformly across, not stuff where we decide whether or not to recurse
//    final ExplorerVisitor visitor = new ExplorerVisitor() {
//
//        List<MAction> actions = new ArrayList<>();
//        MAction current = null;
//        @Override
//        public void preVisit(ExploreNode exploreNode) {
////                        super.preVisit(exploreNode);
//            boolean skip = exploreNode instanceof ModuleNode
//                    || exploreNode instanceof Context
//                    || exploreNode instanceof FormalParamNode;
////                                || (exploreNode instanceof OpDefNode && ((OpDefNode) exploreNode).getBody() == null)
//
//            if (exploreNode instanceof SemanticNode) {
//                TreeNode stn = ((SemanticNode) exploreNode).stn;
//                if (stn == null) {
//                    skip = true;
//                } else {
//                    switch (stn.getFilename()) {
//                        case "--TLA+ BUILTINS--":
//                        case "Naturals":
//                        case "TLC":
//                            skip = true;
//                    }
//                }
//            }
//
//            if (skip) {
//                return;
//            }
//
//            if (exploreNode instanceof OpDefNode) {
//                current = new MAction();
//                System.out.println("action " + ((OpDefNode) exploreNode).getName());
//            } else if (exploreNode instanceof OpApplNode &&
//                    ((OpApplNode) exploreNode).getOperator().getName().equals("$ConjList")) {
//
//
//            } else {
//                System.out.println(exploreNode.getClass());
//            }
//        }
//
//        @Override
//        public void postVisit(ExploreNode exploreNode) {
//            super.postVisit(exploreNode);
//        }
//    };
//                rootModule.walkGraph(new Hashtable<>(), visitor);
////                visitor.done();
//
//                Arrays.stream(tool.getActions()).forEach(a -> {
//        int b = 1;
//    });
}
