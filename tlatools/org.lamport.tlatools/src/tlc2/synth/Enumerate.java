package tlc2.synth;

import tla2sany.semantic.*;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.EvalException;
import tlc2.tool.TLCState;
import tlc2.tool.impl.FastTool;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import util.Assert;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static tlc2.tool.ToolGlobals.OPCODE_exc;

public class Enumerate {
    final FastTool tool;

    Map<String, Tool.TermVal> terms;
    Context ctx;
    TLCState state;

    public Enumerate(FastTool tool, Map<String, Tool.TermVal> terms, Context ctx, TLCState state) {
        this.tool = tool;
        this.terms = terms;
        this.ctx = ctx;
        this.state = state;
    }

    static <T> Stream<List<T>> cartesianProduct(List<List<T>> lists) {
        if (lists.isEmpty()) {
            return Stream.of(new ArrayList<T>());
        } else {
            List<T> firstList = lists.get(0);
            Stream<List<T>> remainingLists = cartesianProduct(lists.subList(1, lists.size()));
            return remainingLists.flatMap(remainingList ->
                    firstList.stream().map(condition -> {
                        ArrayList<T> resultList = new ArrayList<T>();
                        resultList.add(condition);
                        resultList.addAll(remainingList);
                        return resultList;
                    })
            );
        }
    }

    int rank(OpApplNode left) {
        // balance size and generality
        return 1;
    }

    Stream<ExprOrOpArgNode> mutationsRec(ExprOrOpArgNode node, boolean top) {
        if (!(node instanceof OpApplNode)) {
            if (top) {
                return Stream.of(node);
            }
            return Stream.concat(Stream.of(node), terms.values().stream().map(v -> v.term));
        } else {
            OpApplNode n = (OpApplNode) node;
            List<ExprOrOpArgNode> candidates = new ArrayList<>();
            List<List<ExprOrOpArgNode>> args = Arrays.stream(n.getArgs())
                    .map(a -> mutationsRec(a, false).collect(Collectors.toList()))
                    .collect(Collectors.toList());

            // cartesianProduct([]) = {{}}, so there will be one element if this operator
            // has no operands, which causes it to be added once
            cartesianProduct(args).filter(a -> !a.isEmpty()).forEach(a -> {
                OpApplNode m = n.astCopy();
                m.setArgs(a.toArray(new ExprOrOpArgNode[0]));
                candidates.add(m);
            });

            if (top) {
                return candidates.stream();
            }
            return Stream.concat(candidates.stream(), terms.values().stream().map(v -> v.term));
//                        .filter(distinctByKey(Eval::prettyPrint));
        }
    }

    // only mutates at the current level
    Stream<ExprOrOpArgNode> extraMutations(ExprOrOpArgNode node) {
        if (!(node instanceof OpApplNode)) {
            return Stream.of();
        } else {
            OpApplNode n = (OpApplNode) node;
            if (n.getArgs().length == 0) {
                return Stream.of();
            }
            // TODO don't return singleton?
            // TODO we create an invalid EXCEPT

            int argCount;
            if (BuiltInOPs.getOpCode(n.getOperator().getName()) == OPCODE_exc) {
                argCount = 3;
            } else {
                argCount = n.getArgs().length;
            }

            List<ExprOrOpArgNode> candidates = new ArrayList<>();
            List<List<ExprOrOpArgNode>> args = IntStream.range(0, argCount)
                    .mapToObj(i -> terms.values().stream()
                            .map(v -> (ExprOrOpArgNode) v.term)
                            .collect(Collectors.toList()))
                    .collect(Collectors.toList());

            // cartesianProduct([]) = {{}}, so there will be one element if this operator
            // has no operands, which causes it to be added once
            cartesianProduct(args).filter(a -> !a.isEmpty()).forEach(a -> {
                OpApplNode m = n.astCopy();
                if (BuiltInOPs.getOpCode(n.getOperator().getName()) == OPCODE_exc) {
                    OpApplNode pair = (OpApplNode) n.getArgs()[1].astCopy();
                    OpApplNode idx;
                    if (pair.getArgs()[0] instanceof OpApplNode) {
                        idx = ((OpApplNode) pair.getArgs()[0]).astCopy();
                        idx.setArgs(new ExprOrOpArgNode[]{a.get(1)});
                    } else {
                        idx = (OpApplNode) a.get(1);
                    }
                    pair.setArgs(new ExprOrOpArgNode[]{idx, a.get(2)});
                    m.setArgs(new ExprOrOpArgNode[]{a.get(0), pair});
//                        m.setArgs(a.toArray(ExprOrOpArgNode[]::new));
                } else {
                    m.setArgs(a.toArray(ExprOrOpArgNode[]::new));
                }
                candidates.add(m);
            });

//                List<String> collect = candidates.stream().map(a -> prettyPrint(a)).collect(Collectors.toList());

//                if (top) {
            return candidates.stream();
//                }
//                return Stream.concat(candidates.stream(), components.values().stream().map(v -> v.term));
//                        .filter(distinctByKey(Eval::prettyPrint));
        }
    }

    Stream<List<OpApplNode>> product(int n) {
        List<List<OpApplNode>> c = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            c.add(this.terms.values().stream().map(a -> a.term).toList());
        }
        return cartesianProduct(c);
    }

    // compute next frontier
    void search(IValue target) {
        Map<String, Tool.TermVal> additions = new HashMap<>();

        System.out.println("level 0");
        // the zeroth level: mutating components
        terms.keySet().forEach(k -> {
            System.out.println(k);
        });
        for (Map.Entry<String, Tool.TermVal> entry : terms.entrySet()) {
            System.out.println("(" + terms.size() + ") generating mutations of " + Eval.prettyPrint(entry.getValue().term));
            List<ExprOrOpArgNode> mut = extraMutations(entry.getValue().term).collect(Collectors.toList());

//                List<String> debug1 = mut.stream().map(Eval::prettyPrint).collect(Collectors.toList());
            for (ExprOrOpArgNode m : mut) {
                String debug = Eval.prettyPrint(m);
                try {
                    IValue res = tool.eval(m, ctx, state);
                    System.out.printf("%s ==> %s\n", Eval.prettyPrint(m), res);

                    boolean better = true;
                    if (better) {
                        // TODO cast for now
                        // don't save these values as the component set grows too quickly, and most are not valuable
//                            additions.put(prettyPrint(res), new Tool.TermVal((OpApplNode) m, res, ctx));
                    }
                    if (Eval.valueEq(res, target)) {
                        break;
                    }
                } catch (Assert.TLCRuntimeException | EvalException e) {
                    // do nothing
//                        System.out.println("invalid " + debug);
                }
            }
        }

        System.out.println("applying rules");
        // apply rules to build new components, then mutate them

        List<List<Function<List<ExprOrOpArgNode>, OpApplNode>>> rules = List.of(
                List.of(Build.unary(Build::setLiteral)),
                List.of(Build.binary(Build.libraryOp(tool, "Sequences", "Append"))));
        top:
        for (int i = 0; i < rules.size(); i++) {
            for (List<OpApplNode> p : (Iterable<List<OpApplNode>>) product(i + 1)::iterator) {
                List<ExprOrOpArgNode> p1 = p.stream()
                        .map(p2 -> (ExprOrOpArgNode) p2)
                        .collect(Collectors.toList());
                // TODO prune non-promising expressions like {{}}?
                //  so we don't keep them as components. hard to identify them though
                for (Function<List<ExprOrOpArgNode>, OpApplNode> r : rules.get(i)) {
                    OpApplNode candidate = r.apply(p1);
                    try {
                        {
                            IValue res = tool.eval(candidate, ctx, state);
                            System.out.printf("%s ==> %s\n", Eval.prettyPrint(candidate), res);

                            boolean better = true;
                            if (better) {
                                additions.put(Eval.prettyPrint(res), new Tool.TermVal(candidate, res, ctx));
                            }
                            if (Eval.valueEq(res, target)) {
                                break top;
                            }
                        }

                        List<ExprOrOpArgNode> mut = extraMutations(candidate).collect(Collectors.toList());

                        for (ExprOrOpArgNode m : mut) {
                            IValue res = tool.eval(m, ctx, state);
                            System.out.printf("%s ==> %s\n", Eval.prettyPrint(m), res);

                            boolean better = true;
                            if (better) {
                                // TODO cast for now
                                additions.put(Eval.prettyPrint(res), new Tool.TermVal((OpApplNode) m, res, ctx));
                            }
                            if (Eval.valueEq(res, target)) {
                                break top;
                            }
                        }

                    } catch (EvalException e) {
                        // not sure if it's worth pruning ill-typed expressions because they're
                        // removed in one traversal, by evaluation
                        // System.out.printf("%s =/=>\n", candidate.prettyPrint());
                    }
                }
            }
        }

        // commit all changes
        System.out.println("COMMIT");
        terms.putAll(additions);
    }

    static class Stop extends RuntimeException {
        private final Control c;
        public Stop(Control c) {
            this.c = c;
        }
    }


    Control search(Map<String, ExprOrOpArgNode> terms, BiConsumer<ExprOrOpArgNode, Integer> f) {
        try {
            enumerateGrammar(terms, f, 1);
            throw new IllegalStateException();
        } catch (Stop e) {
            return e.c;
        }
    }

    void enumerateGrammar(Map<String, ExprOrOpArgNode> terms, BiConsumer<ExprOrOpArgNode, Integer> f, int depth) {
        Map<String, ExprOrOpArgNode> terms1 = new HashMap<>(terms);
        Consumer<ExprOrOpArgNode> f1 = t -> {
            terms1.put(Eval.prettyPrint(t), t);
            f.accept(t, depth);
        };
        terms.forEach((_k, t) -> {
//            f1.accept(Build.tla("+", t, Build.number(1)));
            f1.accept(Build.libraryOp(tool, "Naturals", "+").apply(t, Build.number(1)));
            // binary
            terms.forEach((_k1, t1) -> {
                // TODO don't accept just about anything for the index?
                f1.accept(Build.fnApp(t, t1));
                f1.accept(Build.libraryOp(tool, "Sequences", "Append").apply(t, t1));
                f1.accept(Build.libraryOp(tool, "Sequences", "\\o").apply(t, t1));
            });
        });
        enumerateGrammar(terms1, f, depth + 1);
    }

//    Stream<ExprOrOpArgNode> next(Map<String, ExprOrOpArgNode> terms) {
//        return terms.entrySet().stream().flatMap(t ->
//                Stream.concat(
//                        Stream.of(Build.tla("+", t.getValue(), Build.number(1))),
//                        terms.entrySet().stream().flatMap(t1 ->
//                                Stream.of(Build.append(tool).apply(t.getValue(), t1.getValue())))));
//    }

//    Stream<ExprOrOpArgNode> next(Map<String, ExprOrOpArgNode> terms) {
//        terms.values().stream().
//        return terms.entrySet().stream().flatMap(t ->
//                Stream.concat(
//                        Stream.of(Build.tla("+", t.getValue(), Build.number(1))),
//                        terms.entrySet().stream().flatMap(t1 ->
//                                Stream.of(Build.append(tool).apply(t.getValue(), t1.getValue())))));
//    }

    public static class Control {
        public ExprOrOpArgNode term;
        public int candidates = 0;
        public int depth;
        public long startTime = System.currentTimeMillis();
        public long ms;
        public void stop() {
            throw new Stop(this);
        }
        public void giveUp() {
            throw new Stop(null);
        }
    }

    public Control synthesizeStateless(Map<String, ExprOrOpArgNode> seed,
                                                         Consumer<Control> validate) {
        Control control = new Control();
        return search(seed, (t, depth) -> {
            control.depth = depth;
            control.ms = System.currentTimeMillis() - control.startTime;
            ++control.candidates;
//            System.out.printf("%s ==> ", Eval.prettyPrint(t));
            try {
                control.term = t;
                validate.accept(control);
            } catch (Assert.TLCRuntimeException | EvalException e) {
                // continue searching
//                System.out.println("<fail>");
            }
        });
    }

    OpApplNode synthesize1(IValue target) {
        while (true) {
            search(target);
            if (done(target)) {
                System.out.println("done");
                OpApplNode answer = terms.get(target.toString()).term;
                System.out.println(Eval.prettyPrint(answer));
                return answer;
            }
        }
    }

    private boolean done(IValue target) {
        return terms.values().stream().anyMatch(v -> Eval.valueEq(v.value, target));
    }
}
