package tlc2;

import tla2sany.semantic.*;
import tlc2.value.IValue;
import tlc2.value.impl.*;
import util.UniqueString;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static tla2sany.semantic.ASTConstants.*;

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

    static int n = 0;

    static String fresh() {
        return "v" + n++;
    }

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

    public static void convert(Map<UniqueString, IValue> initialState, ModuleNode rootModule) throws Exception {

        String overallTemplate = Objects.requireNonNull(getResourceFileAsString("tlc2/MonitorTemplate.go"));
//        String preTemplate = Objects.requireNonNull(getResourceFileAsString("tlc2/MonitorPreTemplate.go"));
//        String postTemplate = Objects.requireNonNull(getResourceFileAsString("tlc2/MonitorPostTemplate.go"));
//        String variableTemplate = Objects.requireNonNull(getResourceFileAsString("tlc2/MonitorVariableTemplate.go"));

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
            String params = translateParams(d, (i,p) -> String.format("%s any", p.getName().toString()));
            GoBlock body = translateTopLevel(d.getBody());
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
                        .map(d -> {
                                    return String.format("case %1$s:\nif err := m.Check%1$s(%2$si, prev, this); err != nil {\nreturn err\n}",
                                            d.getName().toString(),
                                            translateParams(d, (i,p) -> String.format("this.params[%d]", i)));
                                }
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

    private static boolean isVar(SemanticNode body) {
        return body instanceof OpApplNode && ((OpApplNode) body).getArgs().length == 0;
    }

    private static String getVarName(OpApplNode fml) {
        return fml.getOperator().getName().toString();
    }

    private static boolean isPrimedVar(SemanticNode body) {
        return body instanceof OpApplNode && ((OpApplNode) body).getOperator().getName().equals("'");
    }

    private static boolean isConstant(SemanticNode body) {
        return body instanceof StringNode || body instanceof NumeralNode;
    }

    private static List<ExprOrOpArgNode> operatorArgs(SemanticNode body) {
        if (!(body instanceof OpApplNode)) {
            throw fail("not an operator");
        }
        return new ArrayList<>(Arrays.asList(((OpApplNode) body).getArgs()));
    }

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
    private static GoBlock failure(GoExpr expr, String cond) {
        return goBlock("if !(%s) {\nreturn fail(\"%s failed at %%d; expected %s but got %%s (prev: %%+v, this: %%+v)\", trace_i, prev.state.x, prev, this)\n}",
                expr,
                cond,
                expr);
    }

    /**
     * we only try to split at the top level, for simple actions this produces better code.
     * for complicated cases we don't do anything fancy and produce a single large expression.
     */
    private static GoBlock translateTopLevel(ExprOrOpArgNode op) {

        if (!(op instanceof OpApplNode)) {
            throw fail("not op app node?");
        }


        UniqueString opName = ((OpApplNode) op).getOperator().getName();
        List<ExprOrOpArgNode> args = operatorArgs(op);

        boolean isPost = args.size() >= 2 && (isPrimedVar(args.get(0)) || isPrimedVar(args.get(1)));
        String cond = isPost ? "postcondition" : "precondition";

        if (opName.equals(OP_cl)) {
            return args.stream().map(a -> translateTopLevel(a))
                    .reduce(GoBlock::seq).get();
        }

        if (opName.equals(OP_dl)) {
            List<GoExpr> disjuncts = args.stream().map(a -> translateExpr(a)).collect(Collectors.toList());
            GoBlock res = goBlock("");
            for (int i = disjuncts.size() - 1; i >= 0; i--) {
                GoBlock fail = i == disjuncts.size() - 1 ? failure(disjuncts.get(i), cond) : res;
                res = goBlock("if !(%s) {\n%s\n}\n", disjuncts.get(i), fail);
            }
            return res;
        }

        GoExpr expr = translateExpr(op);
        return failure(expr, cond);
    }

    private static class GoExpr {
        List<String> defs = new ArrayList<>();
        String expr;
    }

    private static class GoBlock {
        String block;

        public GoBlock(String block) {
            this.block = block;
        }

        public GoBlock seq(GoBlock other) {
            return new GoBlock(block + other.block);
        }

        @Override
        public String toString() {
            return block;
        }
    }

//    private static GoExpr goExprDef(String def, String ) {
//        GoExpr res = new GoExpr();
//        res.defs.add(def);
//        res.expr = expr;
//        return res;
//    }

    private static GoExpr goExpr(GoBlock block, String fmt, Object... args) {
        GoExpr res = new GoExpr();
        res.defs.add(block.block);
        GoExpr e = goExpr(fmt, args);
        res.defs.addAll(e.defs);
        res.expr = e.expr;
        return res;
    }

    private static GoExpr joinGoExpr(List<GoExpr> exprs, String s) {
        GoExpr res = new GoExpr();
        res.expr = exprs.stream().map(e -> {
            res.defs.addAll(e.defs);
            return e.expr;
        }).collect(Collectors.joining(s));
        return res;
    }

    /**
     * args may be strings or GoExprs.
     * definitions are accumulated.
     */
    private static GoExpr goExpr(String fmt, Object... args) {
        GoExpr res = new GoExpr();
        Object[] args1 = Arrays.stream(args).flatMap(a -> {
            if (a instanceof String) {
                return Stream.of(a);
            } else if (a instanceof List) {
                throw fail("invalid");
//                return ((List<?>) a).stream().peek(b -> {
//                    // this only goes one level deep
//                    if (b instanceof GoExpr) {
//                        res.defs.addAll(((GoExpr) b).defs);
//                    }
//                });
            } else if (a instanceof GoExpr) {
                res.defs.addAll(((GoExpr) a).defs);
                return Stream.of(((GoExpr) a).expr);
            } else {
                throw fail("invalid");
            }
        }).toArray();
        res.expr = String.format(fmt, args1);
        return res;
    }

    /**
     * printf, but if the arguments are GoExprs, their definitions are taken
     * out and placed at the top of the resulting block.
     */
    private static GoBlock goBlock(String fmt, Object... args) {
        List<String> defs = new ArrayList<>();
        Object[] args1 = Arrays.stream(args).flatMap(a -> {
            if (a instanceof GoExpr) {
                defs.addAll(((GoExpr) a).defs);
                return Stream.of(((GoExpr) a).expr);
            } else if (a instanceof List) {
                throw fail("invalid");
//                return ((List<?>) a).stream().peek(b -> {
//                    // this only goes one level deep
//                    if (b instanceof GoExpr) {
//                        defs.addAll(((GoExpr) b).defs);
//                    }
//                });
            }
            return Stream.of(a);
        }).toArray();
        return new GoBlock(String.join("", defs) + "\n" + String.format(fmt, args1));
    }

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

    enum Type {
        INT
    }

    static String goTypeName(Type typ) {
        switch (typ) {
            case INT:
                return "int";
        }
        fail("unhandled " + typ);
        return null;
    }

    private static GoExpr translateExpr(ExprOrOpArgNode fml) {
        return translateExpr(fml, null);
    }

    private static GoExpr translateExpr(ExprOrOpArgNode fml, Type typ) {
        if (isConstant(fml)) {
            if (fml instanceof StringNode) {
                return goExpr("\"" + ((StringNode) fml).getRep().toString() + "\"");
            } else if (fml instanceof NumeralNode) {
                return goExpr(((NumeralNode) fml).val() + "");
            }
            throw fail("unknown");
        } else if (isVar(fml) || isPrimedVar(fml)) {
            if (getVarName((OpApplNode) fml).equals("TRUE")) {
                return goExpr("true");
            } else if (getVarName((OpApplNode) fml).equals("FALSE")) {
                return goExpr("false");
            }
            String v = isPrimedVar(fml) ? "this" : "prev";
            String name = isPrimedVar(fml)
                    ? getVarName((OpApplNode) operatorArgs(fml).get(0))
                    : getVarName((OpApplNode) fml);
//            if (name.equals("$Tuple")) {
//                // somehow empty sequences land in here
//                return goExpr("[]any{}");
//            }
            if (typ == null) {
                return goExpr("%s.state.%s", v, name);
            } else {
                return goExpr("%s.state.%s.(%s)", v, name, goTypeName(typ));
            }
//            return name;
//        } else if (isPrimedVar(fml)) {
//            List<ExprOrOpArgNode> args = operatorArgs(fml);
//            return translateExpr(args.get(0));
        } else if (fml instanceof OpApplNode) {
            String name = ((OpApplNode) fml).getOperator().getName().toString();
            List<ExprOrOpArgNode> args = operatorArgs(fml);
            switch (name) {
                case "<":
                case "<=":
                case ">":
                case ">=":
                case "+":
                case "-":
                case "*":
                case "/":
                    return goExpr("%s %s %s",
                            translateExpr(args.get(0), Type.INT),
                            name, translateExpr(args.get(1), Type.INT));
                case "=":
                    return goExpr("reflect.DeepEqual(%s, %s)",
                            translateExpr(args.get(0)), translateExpr(args.get(1)));
                case "/=":
                    return goExpr("!reflect.DeepEqual(%s, %s)",
                            translateExpr(args.get(0)), translateExpr(args.get(1)));
                case "Some":
                    return goExpr("[]interface{}{%s}", translateExpr(args.get(0)));
                case "Append":
                    return goExpr("append(%s, %s)", translateExpr(args.get(0)), translateExpr(args.get(1)));
                case "ToSet":
                    String v = fresh();
                    GoExpr a1 = translateExpr(args.get(0));
                    GoBlock def = goBlock("%s := map[interface{}]bool{}\nfor _, v := range %s {\n%s[v] = true\n}", v, a1, v);
                    return goExpr(def, "%s", v);
                case "$FcnApply":
                    GoExpr map = translateExpr(args.get(0));
                    GoExpr key = translateExpr(args.get(1));
                    return goExpr("%s[%s]", map, key);
                case "$SetEnumerate":
                    List<GoExpr> exprs = args.stream().map(Monitoring::translateExpr).collect(Collectors.toList());
                    return goExpr("map[interface{}]bool{%s}", joinGoExpr(exprs, ", "));
                case "$RcdConstructor":
                    List<GoExpr> all = args.stream().map(a -> {
                        OpApplNode op = (OpApplNode) a;
                        if (op.getOperator().getName().equals("$Pair")) {
                            List<ExprOrOpArgNode> args1 = operatorArgs(op);
                            return goExpr("%s: %s",
                                    translateExpr(args1.get(0)),
                                    translateExpr(args1.get(1)));
                        } else {
                            throw fail("unexpected");
                        }
                    }).collect(Collectors.toList());
                    return goExpr("map[string]interface{}{%s}", joinGoExpr(all, ", "));
                case "$DisjList":
                case "\\or":
                    return args.stream().map(Monitoring::translateExpr)
                            .reduce((a, b) -> goExpr("(%s || %s)", a, b))
                            .get();
                case "$ConjList":
                case "\\land":
                    return args.stream().map(Monitoring::translateExpr)
                            .reduce((a, b) -> goExpr("(%s && %s)", a, b))
                            .get();
                case "$Except":
                    throw fail("handled at a higher level");
                case "UNCHANGED":
                    if (((OpApplNode) args.get(0)).getOperator().getName().equals("$Tuple")) {
                        return translateExpr(tla(OP_cl, args.stream().map(a -> tla("UNCHANGED", a)).toArray(ExprOrOpArgNode[]::new)));
                    }
                    ExprOrOpArgNode var = args.get(0);
                    OpApplNode equal = tla("=", tla(OP_prime, var), var);
                    return translateExpr(equal);
                default:
                    throw fail("translateExpr: unknown? " + name);
            }
        }
        throw fail("translateExpr: unknown? " + fml);
    }

    /**
     * Builds TLA+ expressions
     */
    private static OpApplNode tla(UniqueString op, ExprOrOpArgNode... args) {
        OpDefNode def = new OpDefNode(op);
        OpApplNode app = new OpApplNode(def);
        app.setArgs(args);
        return app;
    }

    private static OpApplNode tla(String op, ExprOrOpArgNode... args) {
        return tla(UniqueString.uniqueStringOf(op), args);
    }

    private static RuntimeException fail(String s) {
        RuntimeException e = new RuntimeException(s);
        e.printStackTrace();
        return e;
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
