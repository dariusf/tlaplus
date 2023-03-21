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

    static Set<String> simpleDiff(State a, State b) {
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

    static class RankedState {
        State state;
        Set<String> changedFields;
        State proj;
        int score;

        public RankedState(State state, Set<String> changedFields, State proj, int score) {
            this.state = state;
            this.changedFields = changedFields;
            this.proj = proj;
            this.score = score;
        }

        @Override
        public String toString() {
            return String.format("%s %s %d",
                    ((TupleValue) state.data.get("actions")).getLast(),
                    state.data.get("who"), score);
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

    public static void showCounterexample(Cex mbtc) {
        // good contains all variables in the model.
        // bad/impl contains a subset, where absence means not exposed (and not necessarily unchanged).
        State goodGlobal = mbtc.goodState();
        Event badProj = mbtc.badState();

        StringValue actor = new StringValue(badProj.who);
        StringValue network = new StringValue("Network");

        // project on current actor, and limit fields to those in the impl state
        State goodProj = projectLimit(goodGlobal, badProj.toState(), actor);

        // what changed from goodProj -> bad (i.e. what was observed to happen)
        Set<String> implChanged = simpleDiff(goodProj, badProj.toState());

        System.out.println("---\nfrontier states");
//        System.out.println("* frontier states");

        // pick the state in the frontier with the smallest diff from what happened
        List<RankedState> ranked = mbtc.frontier.stream()
//                .filter(s ->
//                // subset of frontier relevant to the current actor
//                s.data.get("who").equals(actor) || s.data.get("who").equals(network)
//        )
                .map(s ->
                        // diff frontier with global good state
                {
                    State proj = projectLimit(s, badProj.toState(), actor);
                    Set<String> changedFields = simpleDiff(goodProj, proj);

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
//                    return new RankedState(s, simpleDiff(good, s), proj);
                    return new RankedState(s, changedFields, proj, score);
                }).sorted(Comparator.comparing(s ->
                                -s.score

                        // idea: increase the count for variables that are not changed, so we prioritise actions
                        // which change exactly the required variables

//            if (count == 7) {
//                int a = 1;
//            }
//            Set<String> intersect = new HashSet<>(implChanged);
//            intersect.retainAll(s.changedFields);
//            int r = -intersect.size();
//            System.out.println(r);
//            return r;
// TODO test this

                )).collect(Collectors.toList());

//        ranked.forEach(s -> {
//            System.out.println("frontier action name: " + ((TupleValue) s.state.data.get("actions")).getLast());
//            System.out.println("changed in this frontier action:");
//            for (String changedField : s.changedFields) {
//                System.out.println(changedField + ": " + goodProj.data.get(changedField) + " to " + s.proj.data.get(changedField));
//            }
////            System.out.println(count);
////            System.out.println("---");
//        });

//        Map.Entry<State, Set<String>>
        RankedState possibleNext = ranked.get(0);
        IValue nextAction = ((TupleValue) possibleNext.state.data.get("actions")).getLast();
//        new State(new HashMap<>(ranked.get(0).getKey().data));
//        State likely = new State(new HashMap<>(ranked.get(0).getKey().data));
//        likely.data.remove("i");
//        likely.data.remove("who");
//        likely.data.remove("actions");

//        System.out.println("* prefix of behaviour:");
        System.out.println("---\nprefix of behaviour:");
        System.out.printf("%2d. Initial state\n", 0);
        int i=1;
        for (IValue a : ((TupleValue) goodGlobal.data.get("actions")).getElems()) {
            System.out.printf("%2d. %s\n", i, a);
            System.out.printf("    %s %s\n",
                    mbtc.implTrace.get(i).who,
                    mbtc.implTrace.get(i).label);
            i++;
        }
        System.out.printf("---\nstate %d is allowed by the model, but %d (as seen in the impl) is not\n",
                mbtc.prefixI - 1, mbtc.prefixI);
        System.out.printf("%s:%s\n", badProj.file, badProj.line);

        System.out.printf("---\n%d. impl made a transition that saw %s changing:\n",
                mbtc.prefixI, Eval.prettyPrint(actor));
        for (String s : implChanged) {
            System.out.printf("%s: %s to %s\n", s, goodProj.data.get(s), badProj.data.get(s));
        }

//        System.out.printf("* state %d is allowed by the model, but %d (as seen in the impl) is not\n", mbtc.prefix_i - 1, mbtc.prefix_i);

//        System.out.printf("* the closest action is %s\n", Eval.prettyPrint(nextAction));
        System.out.printf("---\nthe closest action is %s\n", Eval.prettyPrint(nextAction));

        // what changed? symmetric difference
        {
//            Set<String> intersect = new HashSet<>(changed);
//            intersect.retainAll(likely.getValue());
//                if (!likely.getValue().contains(s)) {

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

        if (false) {

            System.out.println("\n* new transition, if that's wanted:\n");

            for (Map.Entry<String, Value> e : goodGlobal.data.entrySet()) {
                System.out.printf("/\\ %s = %s\n", e.getKey(), e.getValue());
                if (!badProj.data.containsKey(e.getKey())) {
                    System.out.printf("/\\ UNCHANGED %s\n", e.getKey());
                }
            }
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
//        for (Map.Entry<String, Value> e : good.data.entrySet()) {
//            if (!possibleNext.changedFields.contains(e.getKey())) {
//                System.out.printf("/\\ UNCHANGED %s\n", e.getKey());
//            }
//        }

        System.out.println("ok");

//        frontierDiffs =

        // visit values?

//        List<Integer> original = Arrays.asList(1, 2, 3, 4, 5);
//        List<Integer> revised = Arrays.asList(2, 3, 4, 6);

        if (false) {
            List<Value> original = Arrays.asList(IntValue.ValOne, IntValue.ValZero);
            List<Value> revised = Arrays.asList(IntValue.ValOne, BoolValue.ValFalse);

//            Patch<Value> patch = Patch.generate(original, revised, MeyersDiff.factory().create(Present::valueEqual).computeDiff(original, revised, null), false);
        }

//        static DiffAlgorithmFactory DEFAULT_DIFF =
//        Patch<Integer> patch = DiffUtils.diff(original, revised);

//        for (AbstractDelta<Value> delta : patch.getDeltas()) {
//            System.out.println(delta);
//        }

//        Map<String, String> working = Collections.singletonMap("item", "foo");
//        Map<String, String> base = Collections.singletonMap("item", "bar");

//        Diff diff = javers.compare(tommyOld, tommyNew);

//        DiffNode diff = ObjectDifferBuilder.buildDefault().compare(working, base);

//        List<String> working1 = List.of("a", "item", "bar", "foo");
//        List<String> base1 = List.of("blah", "item", "bar");

//        CustomValueComparator<IntValue> intComparator = new CustomValueComparator<>() {
//            @Override
//            public boolean equals(IntValue value, IntValue t1) {
//                if (!value.getClass().equals(t1.getClass())) {
//                    return false;
//                }
//                return value.equals(t1);
//            }
//
//            @Override
//            public String toString(IntValue value) {
//                return Eval.prettyPrint(value);
//            }
//        };
//        CustomValueComparator<RecordValue> customRecordComparator = new CustomValueComparator<>() {
//            @Override
//            public boolean equals(RecordValue value, RecordValue t1) {
//                if (!value.getClass().equals(t1.getClass())) {
//                    return false;
//                }
//                return value.equals(t1);
//            }
//
//            @Override
//            public String toString(RecordValue value) {
//                return Eval.prettyPrint(value);
//            }
//        };
//        CustomValueComparator<Value> customValueComparator = new CustomValueComparator<>() {
//            @Override
//            public boolean equals(Value value, Value t1) {
//                if (!value.getClass().equals(t1.getClass())) {
//                    return false;
//                }
//                return value.equals(t1);
//            }
//
//            @Override
//            public String toString(Value value) {
//                return Eval.prettyPrint(value);
//            }
//        };
//        Javers javers = JaversBuilder.javers()
//
////                .registerValue(Value.class, customValueComparator)
////                .registerValue(RecordValue.class, customRecordComparator)
////                .registerValue(IntValue.class, intComparator)
////                .registerCustomType()
//
//                .registerCustomType(State.class, new CustomPropertyComparator<>() {
//                    @Override
//                    public Optional<PropertyChange> compare(State left, State right, PropertyChangeMetadata metadata, Property property) {
////                        Set<String> commonKeys =
////                        if (equals(left, right)) {
//                            return Optional.empty();
////                        }
////                        return Optional.of(new ValueChange(metadata, left, right));
////                        ArrayList<EntryChange> changes = new ArrayList<>();
////                        new EntryAdd()
////                        return Optional.of(new MapChange(metadata, changes, left, right));
//                    }
//
//                    @Override
//                    public boolean equals(State a, State b) {
////                        if (a.data.keySet().equa)
////                        if (a.data)
////                        return customValueComparator.equals(a.data, b.data);
//                        return false;
//                    }
//
//                    @Override
//                    public String toString(State value) {
////                        return customRecordComparator.toString(value);
//                        return "";
//                    }
//                })
//
//                .registerCustomType(RecordValue.class, new CustomPropertyComparator<>() {
//                    @Override
//                    public Optional<PropertyChange> compare(RecordValue left, RecordValue right, PropertyChangeMetadata metadata, Property property) {
//                        if (equals(left, right)) {
//                            return Optional.empty();
//                        }
//                        return Optional.of(new ValueChange(metadata, left, right));
//                    }
//
//                    @Override
//                    public boolean equals(RecordValue a, RecordValue b) {
//                        return customRecordComparator.equals(a, b);
//                    }
//
//                    @Override
//                    public String toString(RecordValue value) {
//                        return customRecordComparator.toString(value);
//                    }
//                })
//
//                .registerCustomType(IntValue.class, new CustomPropertyComparator<>() {
//                    @Override
//                    public Optional<PropertyChange> compare(IntValue left, IntValue right, PropertyChangeMetadata metadata, Property property) {
//                        if (equals(left, right)) {
//                            return Optional.empty();
//                        }
//                        return Optional.of(new ValueChange(metadata, left, right));
//                    }
//
//                    @Override
//                    public boolean equals(IntValue a, IntValue b) {
//                        return intComparator.equals(a, b);
//                    }
//
//                    @Override
//                    public String toString(IntValue value) {
//                        return intComparator.toString(value);
//                    }
//                })
//
//                .build();
//        System.out.println(javers.getTypeMapping(Value.class).prettyPrint());
//        System.out.println(javers.getTypeMapping(IntValue.class).prettyPrint());
//        System.out.println(javers.getTypeMapping(RecordValue.class).prettyPrint());
//        Diff diff = javers.compare(working1, base1);
//        Diff diff = javers.compare(good, bad);
//        DiffNode diff1 = ObjectDifferBuilder.buildDefault().compare(working, base);
//        System.out.println(diff);
    }

}
