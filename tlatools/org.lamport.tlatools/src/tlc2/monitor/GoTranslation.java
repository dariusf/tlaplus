package tlc2.monitor;

import tla2sany.semantic.*;
import tlc2.synth.Eval;
import tlc2.tool.Defns;
import tlc2.value.IValue;
import tlc2.value.impl.*;
import util.UniqueString;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static tla2sany.semantic.ASTConstants.*;
import static tlc2.monitor.Translate.*;

public class GoTranslation {

    private final Defns defns;
    private final Map<String, IValue> constants;

    // These two fields should be parameters of translateExpr but are here to reduce boilerplate
    public final Set<String> boundVarNames = new HashSet<>();
    private final Stack<Type> typ = new Stack<>();

    public GoTranslation(Defns defns, Map<String, IValue> constants) {
        this.defns = defns;
        this.constants = constants;
    }

    /**
     * we only try to split at the top level, for simple actions this produces better code.
     * for complicated cases we don't do anything fancy and produce a single large expression.
     */
    public GoBlock translateTopLevel(ExprOrOpArgNode op) {

        if (!(op instanceof OpApplNode)) {
            throw fail("not op app node? " + Eval.prettyPrint(op));
        }

        UniqueString opName = ((OpApplNode) op).getOperator().getName();
        List<ExprOrOpArgNode> args = operatorArgs(op);

        boolean isPost = args.size() >= 2 && (isPrimed(args.get(0)) || isPrimed(args.get(1)));
        String cond = isPost ? "postcondition" : "precondition";

        if (opName.equals(OP_cl)) {
            return args.stream().map(a -> translateTopLevel(a))
                    .reduce(GoBlock::seq).get();
        }

        if (opName.equals(OP_dl)) {
            List<GoExpr> disjuncts = args.stream().map(a -> translateExpr(a)).collect(Collectors.toList());
            GoBlock res = goBlock("");
            for (int i = disjuncts.size() - 1; i >= 0; i--) {
                GoBlock fail = i == disjuncts.size() - 1 ? failure(op, disjuncts.get(i), cond) : res;
                res = goBlock("if !(%s) {\n%s\n}\n", disjuncts.get(i), fail);
            }
            return res;
        }

        GoExpr expr = translateExpr(op);
        return failure(op, expr, cond);
    }

    public static GoBlock failure(ExprOrOpArgNode op, GoExpr expr, String cond) {
        return goBlock("if !(%s) {\nreturn fail(\"%s failed at %%d; %s (prev: %%+v, this: %%+v)\", trace_i, prev, this)\n}",
                expr,
                cond,
                Eval.prettyPrint(op)
                        .replaceAll("\\\\", "\\\\\\\\")
                        .replaceAll("\"", "\\\\\""));
    }


    public GoExpr translateExpr(ExprOrOpArgNode fml) {
        if (isConstant(fml)) {
            if (fml instanceof StringNode) {
                return goExpr("\"" + ((StringNode) fml).getRep().toString() + "\"");
            } else if (fml instanceof NumeralNode) {
                return goExpr(((NumeralNode) fml).val() + "");
            }
            throw fail("unknown");
        } else if (fml instanceof OpApplNode) {
            String name = ((OpApplNode) fml).getOperator().getName().toString();
            List<ExprOrOpArgNode> args = operatorArgs(fml);
            switch (name) {
                case "TRUE":
                    return goExpr("true");
                case "FALSE":
                    return goExpr("false");
                case "<":
                case "<=":
                case ">":
                case ">=":
                case "+":
                case "-":
                case "*":
                case "/": {
                    this.typ.push(Type.INT);
                    GoExpr a1 = translateExpr(args.get(0));
                    GoExpr a2 = translateExpr(args.get(1));
                    this.typ.pop();
                    return goExpr("(%s %s %s)", a1, name, a2);
                }
                case "=": {
                    GoExpr a1 = translateExpr(args.get(0));
                    GoExpr a2 = translateExpr(args.get(1));
                    return goExpr("reflect.DeepEqual(%s, %s)", a1, a2);
                }
                case "/=": {
                    GoExpr a1 = translateExpr(args.get(0));
                    GoExpr a2 = translateExpr(args.get(1));
                    return goExpr("!reflect.DeepEqual(%s, %s)",
                            a1, a2);
                }
                case "Some":
                    return goExpr("[]any{%s}", translateExpr(args.get(0)));
                case "None":
                    return goExpr("[]any{}");
                case "Append": {
                    typ.push(Type.SEQ);
                    GoExpr a1 = translateExpr(args.get(0));
                    GoExpr a2 = translateExpr(args.get(1));
                    typ.pop();
                    return goExpr("append(%s, %s)", a1, a2);
                }
                case "ToSet": {
                    String v = fresh();
                    typ.push(Type.SEQ);
                    GoExpr a1 = translateExpr(args.get(0));
                    typ.pop();
                    GoBlock def = goBlock("%s := map[any]bool{}\n" +
                            "for _, v := range %s {\n" +
                            "%s[v] = true\n" +
                            "}", v, a1, v);
                    return goExpr(def, "%s", v);
                }
                case "$FcnApply": {
                    typ.push(Type.RECORD);
                    GoExpr map = translateExpr(args.get(0));
                    typ.pop();
                    typ.push(Type.STRING);
                    GoExpr key = translateExpr(args.get(1));
                    typ.pop();
                    return goExpr("%s[%s]", map, key);
                }
                case "$SetEnumerate": {
                    // {1, 2}
                    List<GoExpr> exprs = args.stream()
                            .map(a -> translateExpr(a))
                            .map(a -> goExpr("%s: true", a)).collect(Collectors.toList());
                    return goExpr("map[any]bool{%s}", joinGoExpr(exprs, ", "));
                }
                case "$Tuple": {
                    // <<>>
                    List<GoExpr> exprs = args.stream()
                            .map(a -> translateExpr(a))
                            .map(a -> goExpr("%s", a)).collect(Collectors.toList());
                    return goExpr("[]any{%s}", joinGoExpr(exprs, ", "));
                }
                case "$RcdConstructor":
                    // [a |-> 1, b |-> 2]
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
                    return goExpr("map[string]any{%s}", joinGoExpr(all, ", "));
                case "$DisjList":
                case "\\or":
                    return args.stream().map(a -> translateExpr(a))
                            .reduce((a, b) -> goExpr("(%s || %s)", a, b))
                            .get();
                case "$ConjList":
                case "\\land":
                    return args.stream().map(a -> translateExpr(a))
                            .reduce((a, b) -> goExpr("(%s && %s)", a, b))
                            .get();
                case "$Except": {
                    // create a new map differing in one element
                    ExprOrOpArgNode unprimed = args.get(0);
                    List<ExprOrOpArgNode> pairArgs = operatorArgs(args.get(1));
                    ExprOrOpArgNode map = operatorArgs(pairArgs.get(0)).get(0);
                    ExprOrOpArgNode key = pairArgs.get(1);
                    String v = fresh();
                    String k1 = fresh();
                    String v1 = fresh();
                    typ.push(Type.RECORD);
                    GoExpr unprimed1 = translateExpr(unprimed);
                    typ.pop();
                    GoExpr map1 = translateExpr(map);
                    GoExpr key1 = translateExpr(key);
                    GoBlock copyMap = goBlock("%1$s := map[any]any{}\n" +
                                    "for %2$s, %3$s := range %4$s {\n" +
                                    "%1$s[%2$s] = %3$s\n" +
                                    "}\n" +
                                    "%1$s[%5$s] = %6$s",
                            v, k1, v1, unprimed1, map1, key1);
                    return goExpr(copyMap, "%s", v);
                }
                case "\\union": {
                    // create a new map with the elements of both
                    ExprOrOpArgNode left = args.get(0);
                    ExprOrOpArgNode right = args.get(1);
                    String v = fresh();
                    String k1 = fresh();
                    String v1 = fresh();
                    String k2 = fresh();
                    String v2 = fresh();
                    typ.push(Type.SET);
                    GoExpr a1 = translateExpr(left);
                    GoExpr a2 = translateExpr(right);
                    typ.pop();
                    GoBlock unionMaps = goBlock("%1$s := map[any]bool{}\n" +
                                    "for %2$s, %3$s := range %6$s {\n%1$s[%2$s] = %3$s\n}\n" +
                                    "for %4$s, %5$s := range %7$s {\n%1$s[%4$s] = %5$s\n}",
                            v, k1, v1, k2, v2, a1, a2);
                    return goExpr(unionMaps, "%s", v);
                }
                case "\\in": {
                    String var = fresh();
                    GoExpr thing = translateExpr(args.get(0));
                    typ.push(Type.SET);
                    GoExpr coll = translateExpr(args.get(1));
                    typ.pop();
                    GoBlock def1 = goBlock("_, %s := %s[%s]", var, coll, thing);
                    return goExpr(def1, "%s", var);
                }
                case "\\notin": {
                    String var = fresh();
                    GoExpr thing = translateExpr(args.get(0));
                    typ.push(Type.SET);
                    GoExpr coll = translateExpr(args.get(1));
                    typ.pop();
                    GoBlock def1 = goBlock("_, %s := %s[%s]", var, coll, thing);
                    return goExpr(def1, "!%s", var);
                }
                case "$FcnConstructor": {
                    // [r \in RM |-> "expr using r"]
                    // create a map and fill it with values from an existing set
                    ExprOrOpArgNode rhs = args.get(0);
                    ExprNode set = ((OpApplNode) fml).getBdedQuantBounds()[0];
                    FormalParamNode var = ((OpApplNode) fml).getQuantSymbolLists().get(0);
                    String v = fresh();
                    String k1 = fresh();
                    String v1 = fresh();
                    ExprOrOpArgNode rhs1 = substitute(rhs, Collections.singletonMap(var, tla(v1)));
                    if (rhs == rhs1) {
                        v1 = "_";
                    }
                    boundVarNames.add(v1);
                    GoExpr a1 = translateExpr(set);
                    typ.push(Type.SET);
                    GoExpr a2 = translateExpr(rhs1);
                    typ.pop();
                    GoBlock unionMaps = goBlock("%1$s := map[any]any{}\n" +
                                    "for %2$s, %3$s := range %4$s {\n%1$s[%2$s] = %5$s\n}\n",
                            v, k1, v1, a1, a2);
                    boundVarNames.remove(v1);
                    return goExpr(unionMaps, "%s", v);
                }
                case "$BoundedForall": {
                    OpApplNode cond = (OpApplNode) args.get(0);
                    // int l = ((OpApplNode) fml).getBdedQuantBounds().length;
                    // TODO this translation assumes l = 1 for simplicity
                    // for (int i = 0; i < l; i++) {
                    ExprNode set = ((OpApplNode) fml).getBdedQuantBounds()[0];
                    GoExpr sset = translateExpr(set);
                    FormalParamNode var = ((OpApplNode) fml).getQuantSymbolLists().get(0);

                    String v = fresh();
                    String k1 = fresh();

                    boundVarNames.add(k1);
                    GoExpr body = translateExpr(substitute(cond, Map.of(var, tla(k1))));
                    boundVarNames.remove(k1);

                    GoBlock b = goBlock("%1$s := true\nfor %2$s, _ := range %3$s {", v, k1, sset)
                            .seq(goBlock("%1$s = %1$s && %4$s\n}", v, k1, sset, body));
                    return goExpr(b, "%s", v);
                }
                case "UNCHANGED": {
                    if (((OpApplNode) args.get(0)).getOperator().getName().equals("$Tuple")) {
                        ExprOrOpArgNode[] tupleArgs = ((OpApplNode) args.get(0)).getArgs();
                        return translateExpr(tla(OP_cl,
                                Arrays.stream(tupleArgs)
                                        .map(a -> tla("UNCHANGED", a))
                                        .toArray(ExprOrOpArgNode[]::new)));
                    }
                    ExprOrOpArgNode var = args.get(0);
                    OpApplNode equal = tla("=", tla(OP_prime, var), var);
                    return translateExpr(equal);
                }
                default:

                    if (boundVarNames.contains(name)) {
                        return goExpr(name);
                    }

                    if (constants.containsKey(name)) {
                        // this gets the values from the config file, then compiles and inlines them.
                        // an alternative is to look them up from what is provided in the monitor?
                        return translateValue(constants.get(name));
                    }

                    // user-defined operator
                    Object userDefined = defns.get(name);
                    if (userDefined instanceof MethodValue) {
                        String s = Eval.prettyPrint(fml);
                        // we used to print a warning, but if the user never discovers the missing operator,
                        // it probably doesn't matter
                        // System.out.println("warning: cannot be translated: " + s);
                        // there's no expression which works in all contexts and lets code compile
                        // return goExpr("/* cannot be translated: %s */", s);
                        throw new CannotBeTranslatedException(s);
                    }
                    if (userDefined != null) {
                        return translateExpr(subst((OpApplNode) fml));
                    }

                    // treat as variable
                    String eventVar = isPrimed(fml) ? "this" : "prev";
                    if (isPrimed(fml)) {
                        name = ((OpApplNode) operatorArgs(fml).get(0)).getOperator().getName().toString();
                    }
                    if (typ.empty()) {
                        return goExpr("%s.state.%s", eventVar, name);
                    } else {
                        return goExpr("%s.state.%s.(%s)", eventVar, name, goTypeName(typ.peek()));
                    }
            }
        }
        throw fail("translateExpr: unknown, non-OpApplNode " + fml);
    }

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
     * this produces an expression, but without defs
     */
    private static GoExpr translateValue(IValue v) {
        if (v instanceof StringValue) {
            return goExpr("\"" + ((StringValue) v).getVal() + "\"");
        } else if (v instanceof IntValue) {
            return goExpr(v.toString());
        } else if (v instanceof SetEnumValue) {
            // empty set
            return goExpr("map[any]bool{}");
        } else if (v instanceof TupleValue) {
            // empty seq
            return goExpr("[]any{}");
        } else if (v instanceof FcnRcdValue) {
            // record literals, like [r1 |-> "working"]
            List<String> res = new ArrayList<>();
            for (int i = 0; i < ((FcnRcdValue) v).domain.length; i++) {
                res.add(String.format("%s: %s",
                        translateValue(((FcnRcdValue) v).domain[i]),
                        translateValue(((FcnRcdValue) v).values[i])));
            }
            return goExpr("map[interface{}]interface{}{%s}", String.join(", ", res));
        }
        throw fail("invalid type of value " + v.getClass().getSimpleName());
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
    static GoBlock goBlock(String fmt, Object... args) {
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

    static String goTypeName(Type typ) {
        switch (typ) {
            case INT:
                return "int";
            case STRING:
                return "string";
            case BOOL:
                return "bool";
            case RECORD:
                return "map[any]any";
            case SEQ:
                return "[]any";
            case SET:
                return "map[any]bool";
        }
        throw fail("goTypeName: unhandled " + typ);
    }

    public OpApplNode subst(OpApplNode app) {
        OpDefNode def = (OpDefNode) defns.get(app.getOperator().getName());
        Map<FormalParamNode, OpApplNode> subs = new HashMap<>();
        for (int i = 0; i < def.getArity(); i++) {
            subs.put(def.getParams()[i], (OpApplNode) app.getArgs()[i]);
        }
        return substitute((OpApplNode) def.getBody(), subs);
    }

}
