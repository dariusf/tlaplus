package tlc2.mbtc;

import tlc2.synth.Eval;
import tlc2.value.IValue;
import tlc2.value.impl.*;
import util.Assert;

import java.nio.file.Files;
import java.nio.file.Paths;
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
            if (b.data.containsKey(e.getKey()) && !valueEqual(e.getValue(), b.data.get(e.getKey()))) {
                res.add(e.getKey());
            }
        }
        return res;
    }

    private static boolean valueEqual(Value a, Value b) {
        if (!a.getClass().equals(b.getClass())) {
            return false;
        }
        try {
            return a.equals(b);
        } catch (Assert.TLCRuntimeException e) {
            return false;
        }
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

    public static void main(String[] args) throws Exception {
        String alignment = "/Users/darius/refinement-mappings/trace-specs/counterexample.json";
        Cex cex = MBTC.gson.fromJson(Files.newBufferedReader(Paths.get(alignment)), Cex.class);
        showCounterexample(cex);
    }

    public static void showCounterexample(Cex cex) {
        // good contains all variables in the model, including auxilaries.
        // bad (projected, from impl) contains a subset, where absence means not exposed
        // (and not necessarily unchanged).
        State goodGlobal = cex.goodState();
        Event badProj = cex.badState();

        StringValue actor = new StringValue(badProj.who);
        StringValue network = new StringValue("Network");

        // project on current actor, and limit fields to those in the impl state
        State goodProj = projectLimit(goodGlobal, badProj.toState(), actor);
        MBTC.ensure(goodProj.data.keySet().equals(badProj.data.keySet()));

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
                if (!valueEqual(possibleNextProj.data.get(s), badProj.data.get(s))) {
                    if (valueEqual(goodProj.data.get(s), possibleNextProj.data.get(s))) {
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

            System.out.println("\n* new transition, if that's wanted:\n");

            for (Map.Entry<String, Value> e : goodGlobal.data.entrySet()) {
//                System.out.printf("/\\ %s = %s\n", e.getKey(), e.getValue());
                if (!badProj.data.containsKey(e.getKey())) {
                    System.out.printf("/\\ UNCHANGED %s\n", e.getKey());
                }
            }

//            given this in bad state
//            /\ currentTerm' = 2
            // /\ currentTerm' = [currentTerm EXCEPT ![who] = ... (expr which evaluates to 2)]
            // only do this for variables which are global

            // TODO need to un-project the bad state into the good one, then synthesise a way to make the change
            for (Map.Entry<String, Value> e : badProj.data.entrySet()) {
//            if (e.getKey().equals("i")) {
//                continue; // TODO filter out these aux vars earlier on
//            }
                if (valueEqual(e.getValue(), goodGlobal.data.get(e.getKey()))) {
                    System.out.printf("/\\ UNCHANGED %s\n", e.getKey());
                } else {
                    // synth an expr to represent change
                    System.out.printf("/\\ %s' = %s\n", e.getKey(), e.getValue());
                }
            }

        }
    }

    private static int scoreFrontierState(Event badProj, StringValue actor, StringValue network, Set<String> implChanged, State s, State proj, Set<String> changedFields) {
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
                if (valueEqual(badProj.data.get(changedField), (proj.data.get(changedField)))) {
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
