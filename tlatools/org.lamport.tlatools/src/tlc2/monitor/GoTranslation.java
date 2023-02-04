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

    // User-defined operators
    private final Defns defns;

    // CONSTANTs overridden in config file
    private final Map<String, IValue> constants;

    // These two fields should be parameters of translateExpr but are here to reduce boilerplate
    // TODO boundVarNames being a mutable set could be problematic if there is shadowing
    public final Set<String> boundVarNames = new HashSet<>();

    public GoTranslation(Defns defns, Map<String, IValue> constants) {
        this.defns = defns;
        this.constants = constants;
    }

    public GoBlock translateInitial(Map<UniqueString, IValue> initial) {
        // this assumes the initial state contains all equalities
        return initial.entrySet().stream().map(e -> {
            GoExpr val = translateValue(e.getValue());
            GoExpr expr = goExpr("reflect.DeepEqual(this.state.%s, %s)",
                    e.getKey().toString(), val);
            return failureMessage("initial",
                    String.format("%s = %s",
                            e.getKey(), Eval.prettyPrint(e.getValue())),
                    String.format("this.state.%s", e.getKey().toString()), val.expr,
                    expr, "precondition");
        }).reduce(GoBlock::seq).get();
    }

    /**
     * We only try to split actions at the top level. For simple actions
     * (a single conj or disj) this produces more granular assertions.
     * We don't do anything special for more complicated cases
     * and produce a single large assertion.
     */
    public GoBlock translateTopLevel(String action, ExprOrOpArgNode op) {

        if (!(op instanceof OpApplNode)) {
            throw fail("translateTopLevel: not OpApplNode: " + Eval.prettyPrint(op));
        }

        UniqueString opName = ((OpApplNode) op).getOperator().getName();
        List<ExprOrOpArgNode> args = operatorArgs(op);

        boolean isPost = args.size() >= 2 && (isPrimed(args.get(0)) || isPrimed(args.get(1)));
        String cond = isPost ? "postcondition" : "precondition";

        if (opName.equals(OP_cl)) {
            return args.stream().map(a -> translateTopLevel(action, a))
                    .reduce(GoBlock::seq).get();
        }

        if (opName.equals(OP_dl)) {
            // once we go through a disjunction, we give up on splitting any subexpressions.
            // the disjunction itself still becomes a series of nested ifs.
            List<GoExpr> disjuncts = args.stream().map(a -> translateExpr(a, null)).collect(Collectors.toList());
            GoBlock res = goBlock("");
            for (int i = disjuncts.size() - 1; i >= 0; i--) {
                GoBlock fail = i == disjuncts.size() - 1 ? failureMessage(action, op, "n/a", "n/a", disjuncts.get(i), cond) : res;
                res = goBlock("if !(%s) {\n%s\n}\n", disjuncts.get(i), fail);
            }
            return res;
        }

        List<String> subexprs = debugSubexpressions(op);
        GoExpr expr = translateExpr(op, null);
        return failureMessage(action, op,
                subexprs.size() > 0 ? subexprs.get(0) : "none",
                subexprs.size() > 1 ? subexprs.get(1) : "none",
                expr, cond);
    }

    public static String escape(String s) {
        return s.replaceAll("\\\\", "\\\\\\\\").replaceAll("\"", "\\\\\"");
    }

    public List<String> debugSubexpressions(ExprOrOpArgNode op) {
        List<String> res = new ArrayList<>();
        String rhs = "\"none\"";
        String lhs = "\"none\"";
        try {
            if (op instanceof OpApplNode) {
                ExprOrOpArgNode[] args = ((OpApplNode) op).getArgs();
                if (args.length > 0) {
                    lhs = translateExpr(args[0], null).expr;
                }
                if (args.length > 1) {
                    lhs = translateExpr(args[1], null).expr;
                }
            }
        } catch (Exception e) {
            // since this is just for debugging, swallow errors and don't fail
            // (it is possible to fail, if we try to look at expressions we didn't create)
        }
        res.add(lhs);
        res.add(rhs);
        return res;
    }

    public static GoBlock failureMessage(String action, ExprOrOpArgNode op, String rhs, String lhs, GoExpr expr, String cond) {
        return failureMessage(action, Eval.prettyPrint(op), lhs, rhs, expr, cond);
    }

    public static GoBlock failureMessage(String action, String op, String lhs, String rhs, GoExpr expr, String cond) {
        return goBlock("if !(%s) {\n" +
                        "return fail(\"%s failed in %s at %%d; %s%%n" +
                        "lhs: %%s%%n" +
                        "rhs: %%s%%n" +
                        "prev: %%+v%%n" +
                        "this: %%+v\"" +
                        ", trace_i, prev, this, %s, %s)\n}",
                expr,
                cond,
                action,
                escape(op),
                lhs, rhs
        );
    }


    public GoExpr translateExpr(ExprOrOpArgNode fml, Type typ) {
        // constants
        if (fml instanceof StringNode) {
            return goExpr("\"" + ((StringNode) fml).getRep().toString() + "\"");
        }
        if (fml instanceof NumeralNode) {
            return goExpr(((NumeralNode) fml).val() + "");
        }

        if (fml instanceof OpApplNode) {
            OpApplNode op = (OpApplNode) fml;
            String name = op.getOperator().getName().toString();
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
                    GoExpr a1 = translateExpr(args.get(0), Type.INT);
                    GoExpr a2 = translateExpr(args.get(1), Type.INT);
                    return goExpr("(%s %s %s)", a1, name, a2);
                }
                case "=": {
                    GoExpr a1 = translateExpr(args.get(0), null);
                    GoExpr a2 = translateExpr(args.get(1), null);
                    return goExpr("reflect.DeepEqual(%s, %s)", a1, a2);
                }
                case "/=": {
                    GoExpr a1 = translateExpr(args.get(0), null);
                    GoExpr a2 = translateExpr(args.get(1), null);
                    return goExpr("!reflect.DeepEqual(%s, %s)",
                            a1, a2);
                }
                case "Some":
                    return goExpr("[]any{%s}", translateExpr(args.get(0), null));
                case "None":
                    return goExpr("[]any{}");
                case "Append": {
                    GoExpr a1 = translateExpr(args.get(0), Type.SEQ);
                    GoExpr a2 = translateExpr(args.get(1), Type.SEQ);
                    return goExpr("append(%s, %s)", a1, a2);
                }
                case "ToSet": {
                    String v = fresh("toset");
                    GoExpr a1 = translateExpr(args.get(0), Type.SEQ);
                    GoBlock def = goBlock("%s := map[any]bool{}\n" +
                            "for _, v := range %s {\n" +
                            "%s[v] = true\n" +
                            "}", v, a1, v);
                    return goExpr(def, "%s", v);
                }
                case "$FcnApply": {
                    // record indexing
                    GoExpr map = translateExpr(args.get(0), Type.RECORD);
                    GoExpr key = translateExpr(args.get(1), Type.STRING);
                    return goExpr("%s[%s]", map, key);
                }
                case "$SetEnumerate": {
                    // {1, 2}
                    String v = fresh("setliteral");
                    GoBlock def = goBlock("%s := map[any]any{}", v);
                    def = args.stream().map(a -> {
                                GoExpr a1 = translateExpr(a, null);
                                return goBlock("%s[hash(%s)] = %s", v, a1, a1);
                            })
                            .reduce(def, GoBlock::seq);
                    return goExpr(def, "%s", v);
                }
                case "$Tuple": {
                    // <<>>
                    List<GoExpr> exprs = args.stream()
                            .map(a -> translateExpr(a, null))
                            .map(a -> goExpr("%s", a)).collect(Collectors.toList());
                    return goExpr("[]any{%s}", joinGoExpr(exprs, ", "));
                }
                case "$RcdConstructor":
                    // [a |-> 1, b |-> 2]
                    List<GoExpr> all = args.stream().map(a -> {
                        OpApplNode op1 = (OpApplNode) a;
                        if (op1.getOperator().getName().equals("$Pair")) {
                            List<ExprOrOpArgNode> args1 = operatorArgs(op1);
                            return goExpr("%s: %s",
                                    translateExpr(args1.get(0), null),
                                    translateExpr(args1.get(1), null));
                        } else {
                            throw fail("unexpected");
                        }
                    }).collect(Collectors.toList());
                    return goExpr("map[any]any{%s}", joinGoExpr(all, ", "));
                case "$DisjList":
                case "\\or":
                    return args.stream().map(a -> translateExpr(a, null))
                            .reduce((a, b) -> goExpr("(%s || %s)", a, b))
                            .get();
                case "$ConjList":
                case "\\land":
                    return args.stream().map(a -> translateExpr(a, null))
                            .reduce((a, b) -> goExpr("(%s && %s)", a, b))
                            .get();
                case "$Except": {
                    // create a new map differing in one element
                    ExprOrOpArgNode unprimed = args.get(0);
                    List<ExprOrOpArgNode> pairArgs = operatorArgs(args.get(1));
                    ExprOrOpArgNode map = operatorArgs(pairArgs.get(0)).get(0);
                    ExprOrOpArgNode key = pairArgs.get(1);
                    String v = fresh("except");
                    String k1 = fresh();
                    String v1 = fresh();
                    GoExpr unprimed1 = translateExpr(unprimed, Type.RECORD);
                    GoExpr map1 = translateExpr(map, null);
                    GoExpr key1 = translateExpr(key, null);
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
                    String v = fresh("union");
                    String k1 = fresh();
                    String v1 = fresh();
                    String k2 = fresh();
                    String v2 = fresh();
                    GoExpr a1 = translateExpr(left, Type.SET);
                    GoExpr a2 = translateExpr(right, Type.SET);
                    GoBlock unionMaps = goBlock("%1$s := map[any]any{}\n" +
                                    "for %2$s, %3$s := range %6$s {\n%1$s[%2$s] = %3$s\n}\n" +
                                    "for %4$s, %5$s := range %7$s {\n%1$s[%4$s] = %5$s\n}",
                            v, k1, v1, k2, v2, a1, a2);
                    return goExpr(unionMaps, "%s", v);
                }
                case "\\in": {
                    String ok = fresh("in");
                    GoExpr elt = translateExpr(args.get(0), null);
                    GoExpr set = translateExpr(args.get(1), Type.SET);
                    GoBlock def1 = goBlock("_, %s := %s[hash(%s)]", ok, set, elt);
                    return goExpr(def1, "%s", ok);
                }
                case "\\notin": {
                    String ok = fresh("notin");
                    GoExpr elt = translateExpr(args.get(0), null);
                    GoExpr set = translateExpr(args.get(1), Type.SET);
                    GoBlock def1 = goBlock("_, %s := %s[hash(%s)]", ok, set, elt);
                    return goExpr(def1, "!%s", ok);
                }
                case "$FcnConstructor": {
                    // [r \in RM |-> "expr using r"]
                    // create a map and fill it with values from an existing set
                    ExprOrOpArgNode rhs = args.get(0);
                    ExprNode set = op.getBdedQuantBounds()[0];
                    FormalParamNode var = op.getQuantSymbolLists().get(0);
                    String v = fresh("fnconstr");
                    String k1 = fresh();
                    String v1 = fresh();
                    ExprOrOpArgNode rhs1 = substitute(rhs, Collections.singletonMap(var, tla(v1)));
                    if (rhs == rhs1) {
                        v1 = "_";
                    }
                    boundVarNames.add(v1);
                    GoExpr a1 = translateExpr(set, null);
                    GoExpr a2 = translateExpr(rhs1, Type.SET);
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
                    ExprNode set = op.getBdedQuantBounds()[0];
                    GoExpr sset = translateExpr(set, null);
                    FormalParamNode var = op.getQuantSymbolLists().get(0);

                    String v = fresh("boundedforall");
                    String k1 = fresh();

                    boundVarNames.add(k1);
                    GoExpr body = translateExpr(substitute(cond, Map.of(var, tla(k1))), null);
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
                                        .toArray(ExprOrOpArgNode[]::new)), null);
                    }
                    ExprOrOpArgNode var = args.get(0);
                    OpApplNode equal = tla("=", tla(OP_prime, var), var);
                    return translateExpr(equal, null);
                }
                default:

                    if (boundVarNames.contains(name)) {
                        return qualifyWithType(goExpr(name), typ);
                    }

                    if (constants.containsKey(name)) {
                        // this gets the values from the config file, then compiles and inlines them.
                        // an alternative is to look them up from what is provided in the monitor?
                        return translateValue(constants.get(name));
                    }

                    // user-defined operator
                    Object userDefined = defns.get(name);
                    if (userDefined instanceof MethodValue) {
                        String s = Eval.prettyPrint(op);
                        // we used to print a warning, but if the user never discovers the missing operator,
                        // it probably doesn't matter
                        // System.out.println("warning: cannot be translated: " + s);
                        // there's no expression which works in all contexts and lets code compile
                        // return goExpr("/* cannot be translated: %s */", s);
                        throw new CannotBeTranslatedException(s);
                    }
                    if (userDefined != null) {
                        return translateExpr(subst(op), null);
                    }

                    // treat as variable
                    String eventVar = isPrimed(op) ? "this" : "prev";
                    if (isPrimed(op)) {
                        name = ((OpApplNode) operatorArgs(op).get(0)).getOperator().getName().toString();
                    }
                    return qualifyWithType(goExpr("%s.state.%s", eventVar, name), typ);
//                    if (typ.empty()) {
//                        return ;
//                    } else {
//                        return goExpr("%s.state.%s.(%s)", eventVar, name, goTypeName(typ.peek()));
//                    }
            }
        }
        throw fail("translateExpr: unknown, non-OpApplNode %s %s",
                fml.getClass().getSimpleName(), Eval.prettyPrint(fml));
    }

    public GoExpr qualifyWithType(GoExpr e, Type typ) {
        if (typ == null) {
            return e;
        } else {
            return goExpr("any(%s).(%s)", e, goTypeName(typ));
        }
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

    public static List<IValue> toList(ValueVec vv) {
        List<IValue> res = new ArrayList<>();
        for (int i = 0; i < vv.size(); i++) {
            res.add(vv.elementAt(i));
        }
        return res;
    }

    /**
     * this produces an expression, but without defs
     */
    public static GoExpr translateValue(IValue v) {
        if (v instanceof StringValue) {
            return goExpr("\"" + ((StringValue) v).getVal() + "\"");
        } else if (v instanceof IntValue) {
            return goExpr(v.toString());
        } else if (v instanceof SetEnumValue) {
            String v1 = fresh("setlit");
            GoBlock def = goBlock("%s := map[any]any{}", v1);
            def = toList(((SetEnumValue) v).elems).stream().map(a -> {
                        GoExpr a1 = translateValue(a);
                        return goBlock("%s[hash(%s)] = %s", v1, a1, a1);
                    })
                    .reduce(def, GoBlock::seq);
            return goExpr(def, "%s", v1);
        } else if (v instanceof TupleValue) {
            List<GoExpr> exprs = Arrays.stream(((TupleValue) v).elems)
                    .map(a -> translateValue(a))
                    .map(a -> goExpr("%s", a)).collect(Collectors.toList());
            return goExpr("[]any{%s}", joinGoExpr(exprs, ", "));
        } else if (v instanceof FcnRcdValue) {
            // record literals, like [r1 |-> "working"]
            List<GoExpr> res = new ArrayList<>();
            for (int i = 0; i < ((FcnRcdValue) v).domain.length; i++) {
                res.add(goExpr("%s: %s",
                        translateValue(((FcnRcdValue) v).domain[i]),
                        translateValue(((FcnRcdValue) v).values[i])));
            }
            return goExpr("map[any]any{%s}", goExprJoin(", ", res));
        }
        throw fail("invalid type of value " + v.getClass().getSimpleName());
    }

    private static GoExpr goExprJoin(String delimiter, List<GoExpr> goExprs) {
        GoExpr res = null;
        boolean first = true;
        for (GoExpr g : goExprs) {
            if (first) {
                res = g;
                first = false;
            } else {
                res.expr += delimiter;
                res.defs.addAll(g.defs);
                res.expr += g.expr;
            }
        }
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
                return "record";
            case SET:
                return "set";
            case SEQ:
                return "seq";
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
