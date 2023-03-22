package tlc2.mbtc;

import tla2sany.semantic.*;
import tlc2.synth.Build;
import tlc2.synth.Enumerate;
import tlc2.synth.Eval;
import tlc2.tool.TLCStateMut;
import tlc2.tool.impl.FastTool;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.impl.*;
import util.UniqueString;

import java.util.*;
import java.util.stream.Collectors;


/**
 * Presentation of counterexamples
 */
public class Present {

    public static State project(State s, StringValue party) {
        State res = new State(new HashMap<>());
        for (Map.Entry<String, Value> e : s.data.entrySet()) {
            if (e.getValue() instanceof RecordValue) {
                Value v = ((RecordValue) e.getValue()).select(party);
                if (v != null) {
                    res.data.put(e.getKey(), v);
                }
            } else {
                // not a record, leave in
                res.data.put(e.getKey(), e.getValue());
            }
        }
        return res;
    }

    static Set<String> simpleFlatDiff(State a, State b) {
        Set<String> res = new HashSet<>();
        for (Map.Entry<String, Value> e : a.data.entrySet()) {
            if (b.data.containsKey(e.getKey()) && !Misc.valueEqual(e.getValue(), b.data.get(e.getKey()))) {
                res.add(e.getKey());
            }
        }
        return res;
    }

    static State projectLimit(State s, State reference, StringValue actor) {
        State g = new State(new HashMap<>());
        s.data.forEach((k, v) -> {
            if (reference.data.containsKey(k)) {
                g.data.put(k, v);
            }
        });
        return project(g, actor);
    }

    public static void showCounterexample(FastTool tool, Cex cex) {
        // good contains all variables in the model, including auxilaries.
        // bad (projected, from impl) contains a subset, where absence means not exposed
        // (and not necessarily unchanged).
        State goodGlobal = cex.goodState();
        ObState badProj = cex.badState();

        StringValue actor = new StringValue(badProj.who);
        StringValue network = new StringValue("Network");

        // project on current actor, and limit fields to those in the impl state
        State goodProj = projectLimit(goodGlobal, badProj.toState(), actor);
        Misc.ensure(goodProj.data.keySet().equals(badProj.data.keySet()));

        // what changed from goodProj -> badProj (i.e. what was observed to happen)
        Set<String> implChanged = simpleFlatDiff(goodProj, badProj.toState());

        System.out.println("---\nfrontier states");
//        System.out.println("* frontier states");

        // pick the state in the frontier with the smallest diff from what happened
        List<RankedState> ranked = cex.frontier.stream()
                .map(s -> {
                    // project frontier and diff with projected good state
                    State proj = projectLimit(s, badProj.toState(), actor);
                    Set<String> changedFields = simpleFlatDiff(goodProj, proj);
                    int score = scoreFrontierState(badProj, actor, network, implChanged, s, proj, changedFields);
                    return new RankedState(s, changedFields, proj, score);
                })
                .sorted(Comparator.comparing(s -> -s.score))
                .collect(Collectors.toList());

        // assume there is at least one non-stuttering state in the frontier
        RankedState possibleNext = ranked.get(0);
        IValue nextAction = ((TupleValue) possibleNext.state.data.get("actions")).getLast();

        // summarize what happened
//        System.out.println("* prefix of behaviour:");
        System.out.println("---\nprefix of behaviour:");
        System.out.printf("%2d. Initial state\n", 0);
        int i = 1;
        for (IValue a : ((TupleValue) goodGlobal.data.get("actions")).getElems()) {
            System.out.printf("%2d. %s\n", i, a);
            System.out.printf("    %s %s\n",
                    cex.implTrace.get(i).who,
                    cex.implTrace.get(i).label);
            i++;
        }

        // explain the diverging state
        System.out.printf("---\nstate %d is allowed by the model, but %d (as seen in the impl) is not\n",
                cex.prefixI - 1, cex.prefixI);
        System.out.printf("%s:%s\n", badProj.file, badProj.line);

        System.out.printf("---\n%d. impl made a transition that saw %s changing:\n",
                cex.prefixI, Eval.prettyPrint(actor));
        for (String s : implChanged) {
            System.out.printf("%s: %s to %s\n", s, goodProj.data.get(s), badProj.data.get(s));
        }

        // find and explain the closest action in the frontier
//        System.out.printf("* the closest action is %s\n", Eval.prettyPrint(nextAction));
        System.out.printf("---\nthe closest action in the frontier is %s\n", Eval.prettyPrint(nextAction));
        {
            State possibleNextProj = project(possibleNext.state, actor);

            implChanged.forEach(s -> {
                // the next state will have values for everything
                assert possibleNextProj.data.containsKey(s);
                if (!Misc.valueEqual(possibleNextProj.data.get(s), badProj.data.get(s))) {
                    if (Misc.valueEqual(goodProj.data.get(s), possibleNextProj.data.get(s))) {
                        System.out.printf("%s changed from\n  %s\nto\n  %s\nbut it should have remained unchanged\n", s, Eval.prettyPrint(goodProj.data.get(s)), Eval.prettyPrint(badProj.data.get(s)));
                    } else {
                        System.out.printf("%s changed from\n  %s\nto\n  %s\nbut it should have changed to\n  %s\ninstead\n", s, Eval.prettyPrint(goodProj.data.get(s)), Eval.prettyPrint(badProj.data.get(s)), Eval.prettyPrint(possibleNextProj.data.get(s)));
                    }
                }
            });
            possibleNext.changedFields.forEach(k -> {
                // remove some aux vars
                if (k.equals("who") || k.equals("actions")) {
                    return;
                }
                // would have been handled earlier
                if (implChanged.contains(k)) {
                    return;
                }
                if (badProj.data.containsKey(k)) {
                    System.out.printf("%s did not change but it should have changed from\n  %s\nto\n  %s\n", k, Eval.prettyPrint(project(goodGlobal, actor).data.get(k)), Eval.prettyPrint(possibleNextProj.data.get(k)));
                }
            });
        }

        // try to add a transition
        if (true || false) {

            System.out.println("\n* new transition:\n");

            // TODO factor this out
            // TODO
            for (Map.Entry<String, Value> e : goodGlobal.data.entrySet()) {
                // TODO constrain only this node's vars
                System.out.printf("/\\ %s = %s\n", e.getKey(), e.getValue());
                if (!badProj.data.containsKey(e.getKey())) {
                    System.out.printf("/\\ UNCHANGED %s\n", e.getKey());
                }
                // TODO figure out a grouping of variables to use. build a tree of those expressions
            }

            Enumerate enumerate = new Enumerate(tool, null, null, null);

            // The variables are already set by loading the spec via a Tool,
            // so we just have to provide the right order...
            TLCStateMut goodState = new TLCStateMut(
                    Arrays.stream(tool.getInitStates().elementAt(0).getVars())
                            .map(o -> goodGlobal.data.get(o.getName().toString()))
                            .toArray(Value[]::new));

            for (Map.Entry<String, Value> e : badProj.data.entrySet()) {

                StringNode who = Build.stringLiteral(badProj.who);

                // TODO seed constants
                // TODO seed params
                // TODO may have more seeds as rules are applied
                Map<String, ExprOrOpArgNode> seed =
//                    Arrays.stream(goodState.getVarsAsStrings())
                        // TODO is this the right place to filter these aux vars?
                        goodGlobal.data.keySet().stream()
                                .filter(v -> !Set.of("i", "actions").contains(v))
                                .map(v -> Build.fnApp(Build.op(v), who))
                                .collect(Collectors.toMap(s -> Eval.prettyPrint(s), s -> s));

//                seed.put(Eval.prettyPrint(who), who);

                seed.put(Eval.prettyPrint(e.getValue()), valueToOpAppl(e.getValue()));

                // horrible hacks
//                seed.put(Eval.prettyPrint(e.getValue()), Build.op("valueItself"));
//                OpDefNode valueItself = new OpDefNode(UniqueString.uniqueStringOf("valueItself"));
//                valueItself.setBody(e.getValue());
//                Context context = Context.Empty.cons(valueItself, e.getValue());

                if (Misc.valueEqual(e.getValue(), goodProj.data.get(e.getKey()))) {
                    System.out.printf("/\\ UNCHANGED %s\n", e.getKey());
                    continue;
                }

                // target would be acceptable, but we want to synthesize something more general
                Value target = e.getValue();
                Enumerate.Control synthesized = enumerate.synthesizeStateless(seed, c -> {
//                    OpApplNode candidate = Build.except(Build.op(e.getKey()), Build.stringLiteral(badProj.who), c.term);
                    // TODO this printing is just for debugging for now

//                    if (e.getKey().equals("log")) {
//                        System.out.printf("%s\n", Eval.prettyPrint(c.term));
//                    }

//                    if (e.getKey().equals("log") && c.candidates % 50 == 0) {
//                        int a = 1;
//                    }
//                    if (
////                            Eval.prettyPrint(c.term).contains("currentTerm[\"s2\"]")
////                    && Eval.prettyPrint(c.term).contains("+")
//                                    Eval.prettyPrint(c.term).contains("currentTerm[\"s2\"] + 1")
//                    ) {
//                        System.out.printf("%s\n", Eval.prettyPrint(c.term));
//                        int a = 1;
//                    }

                    long timeout = 3 * 1000;
                    if (c.ms > timeout || c.candidates > 400_000) {
                        System.out.printf("\\* gave up on %s after %ds and %s candidates, depth %s\n",
                                e.getKey(), timeout / 1000, c.candidates, c.depth);
                        c.giveUp();
                    }

                    if (Eval.prettyPrint(c.term).startsWith("Append(log[\"s2\"], <<")) {
                        int a = 1;
                    }
                    IValue v = tool.eval(c.term, Context.Empty, goodState);
                    // some heuristics:
                    // has to use its own variable
                    // cannot use only its own variable
                    String itself = String.format("%s[%s]", e.getKey(), Eval.prettyPrint(who));
                    if (Eval.prettyPrint(c.term).equals(itself)) {
                        return;
                    }
                    if (!Eval.prettyPrint(c.term).contains(e.getKey())) {
                        return;
                    }
                    if (Eval.valueEq(v, target)) {
                        c.stop();
                    }
                });

                if (synthesized.term != null) {
//                    System.out.println("FOUND! " + Eval.prettyPrint(Build.except(Build.op(e.getKey()), Build.stringLiteral(badProj.who), synthesized.get())));
                    OpApplNode res = Build.except(Build.op(e.getKey()), Build.stringLiteral(badProj.who), synthesized.term);
//                    System.out.println("FOUND! " + Eval.prettyPrint(res));
                    System.out.printf("/\\ %s' = %s\n", e.getKey(), Eval.prettyPrint(res));
                } else {
                    System.out.printf("/\\ %s' = %s\n", e.getKey(), Eval.prettyPrint(target));
                }
            }

//            for (Map.Entry<String, Value> e : badProj.data.entrySet()) {
////            if (e.getKey().equals("i")) {
////                continue; // TODO filter out these aux vars earlier on
////            }
//                if (Misc.valueEqual(e.getValue(), goodGlobal.data.get(e.getKey()))) {
//                    System.out.printf("/\\ UNCHANGED %s\n", e.getKey());
//                } else {
//                    // target would be acceptable, but we want to synthesize something more general
//                    Value target = e.getValue();
//                    System.out.printf("/\\ %s' = %s\n", e.getKey(), target);
//                }
//            }

        }
    }

    private static ExprOrOpArgNode valueToOpAppl(Value value) {
        if (value instanceof IntValue) {
            return Build.number(((IntValue) value).val);
        }
        if (value instanceof StringValue) {
            return Build.stringLiteral(((StringValue) value).val.toString());
        }
        if (value instanceof SetEnumValue) {
            return Build.setLiteral(
                    Arrays.stream(((SetEnumValue) value).elems.toArray())
                            .map(Present::valueToOpAppl)
                            .toArray(ExprOrOpArgNode[]::new));
        }
        if (value instanceof TupleValue) {
            return Build.seq(
                    Arrays.stream(((TupleValue) value).elems)
                            .map(Present::valueToOpAppl)
                            .toArray(ExprOrOpArgNode[]::new));
        }
        if (value instanceof RecordValue) {
            List<ExprOrOpArgNode> names = Arrays.stream(((RecordValue) value).names)
                    .map(n -> Build.stringLiteral(n.toString()))
                    .collect(Collectors.toList());
            List<ExprOrOpArgNode> values = Arrays.stream(((RecordValue) value).values)
                    .map(v -> valueToOpAppl(v))
                    .collect(Collectors.toList());
            List<ExprOrOpArgNode> all = new ArrayList<>();
            for (int i=0; i< names.size(); i++) {
                all.add(names.get(i));
                all.add(values.get(i));
            }
            return Build.record(all.toArray(ExprOrOpArgNode[]::new));
        }
        throw new IllegalStateException();
    }

    private static int scoreFrontierState(ObState badProj, StringValue actor, StringValue network, Set<String> implChanged, State s, State proj, Set<String> changedFields) {
        int score = 0;
//            System.out.println("* frontier action name: " + ((TupleValue) s.data.get("actions")).getLast());
        // FRONTIER HEURISTIC DEBUGGING
        System.out.println("---\n" + ((TupleValue) s.data.get("actions")).getLast());
        if (s.data.get("who").equals(actor) || s.data.get("who").equals(network)) {
            System.out.println("+3 for pertaining to current actor or network");
            score += 3;
        }
        for (String changedField : implChanged) {
            if (changedFields.contains(changedField)) {
                System.out.println("+1 for " + changedField);
                score++;
//                    System.out.println("same field " + changedField);
                if (Misc.valueEqual(badProj.data.get(changedField), (proj.data.get(changedField)))) {
                    System.out.println("+2 for " + badProj.data.get(changedField));
//                        System.out.println("equal value");
                    score += 2;
                }
            }
        }
        for (String changedField : changedFields) {
            if (!implChanged.contains(changedField)) {
                score--;
                System.out.println("-1 for irrelevant var " + changedField);
            }
        }
        System.out.println("total: " + score);
        return score;
    }


}
