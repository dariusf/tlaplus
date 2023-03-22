package tlc2.synth;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import tla2sany.semantic.*;
import tlc2.TLCGlobals;
import tlc2.module.Json;
import tlc2.tool.*;
import tla2sany.parser.TLAplusParser;
import tlc2.tool.impl.FastTool;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.StringValue;
import util.*;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

import static tla2sany.semantic.ASTConstants.OpApplKind;
import static tlc2.tool.ToolGlobals.*;

public class Eval {

    public Eval() {
    }

    public static String prettyPrint(ExprOrOpArgNode node) {
        return node.accept(new PrettyPrintVisitor());
    }

    public static String prettyPrint(IValue v) {
        return v.toString();
    }

    public static boolean valueEq(IValue v1, IValue v2) {
        return prettyPrint(v1).equals(prettyPrint(v2));
    }

    private void modify(SemanticNode node, Context ctx, TLCStateMut goodState) {

//        ExprOrOpArgNode[] args = expr.getArgs();
//        SymbolNode opNode = expr.getOperator();
//        int opcode = BuiltInOPs.getOpCode(opNode.getName());

        if (node.getKind() == OpApplKind) {
            OpApplNode thisNode = (OpApplNode) node;
            int opCode = BuiltInOPs.getOpCode(thisNode.getOperator().getName());
            ExprOrOpArgNode[] args = thisNode.getArgs();

            if (opCode == OPCODE_cl || opCode == OPCODE_dl) {
                Arrays.stream(args).forEach(a -> {
                    // TODO return something to capture the effect of this branch
                    // recurse in left child, then recurse in right child?
                    modify(a, ctx, goodState);
                });
            } else if (opCode == OPCODE_eq || opCode == OPCODE_in) {
                SymbolNode var = tool.getPrimedVar(args[0], ctx, true);
                if (var == null) {
                    // eval this expr to make sure this is true, else terminate this branch
                    // TODO note ordering... if an edit is made and then a child branch evaluates to true.
                    //  one way to fix is if we traverse in order and only cut off a branch at the end
                    IValue eval = tool.eval(thisNode, ctx, goodState);
                    if (eval instanceof BoolValue && ((BoolValue) eval).getVal()) {
                        // allow this branch
                    }
                    // else terminate this branch
                    int a = 1;
                } else if (var.getName().toString().equals("votesGranted")) { // TODO
                    // replace branch with disjunction
                    // TODO produce an edit object
                    // TODO \in should be edited differently
                    SymbolNode op1 = new OpDefNode(OP_dl);
                    OpApplNode newNode = thisNode;

                    // TODO clone object
                    ExprOrOpArgNode setEnum = ((OpApplNode) ((OpApplNode) newNode.getArgs()[1]).getArgs()[1]).getArgs()[1];
                    // TODO grammar
                    // synthesis subproblems
                    // replace with existing component
                    ((OpApplNode) setEnum).setArgs(new ExprOrOpArgNode[]{
                            tool.observed.get("i").term});
                    // eval the right side of the primed assignment
                    IValue synthRes = tool.eval(newNode.getArgs()[1], ctx, goodState);
                    // a builtin operator
                    {
                        SymbolNode emptySetDef = new OpDefNode(OP_se);
                        OpApplNode emptySet = new OpApplNode(emptySetDef, new ExprOrOpArgNode[]{tool.observed.get("i").term});
                        ((OpApplNode) setEnum).setArgs(new ExprOrOpArgNode[]{emptySet});
                    }
                    IValue synthRes1 = tool.eval(newNode.getArgs()[1], ctx, goodState);
                    // an existing lib operator like Append
                    {
                        OpDefNode appendDef = (OpDefNode) tool.getModule("Sequences").getDefinitions().stream()
                                .filter(op -> op instanceof OpDefNode && ((OpDefNode) op).getName().equals("Append"))
                                .findAny().get();
                        SymbolNode emptySeqDef = new OpDefNode(OP_tup);
                        OpApplNode emptySeq = new OpApplNode(emptySeqDef,
                                new ExprOrOpArgNode[]{});
                        OpApplNode appendUse = new OpApplNode(appendDef,
                                new ExprOrOpArgNode[]{emptySeq, emptySeq});
                        ((OpApplNode) setEnum).setArgs(new ExprOrOpArgNode[]{appendUse});
                    }
                    IValue synthRes2 = tool.eval(newNode.getArgs()[1], ctx, goodState);

                    ExprOrOpArgNode[] operands = new ExprOrOpArgNode[]{thisNode, newNode};

                    OpApplNode op = new OpApplNode(op1, operands);
                    String s = prettyPrint(op);

                    int a = 1;
                }
                // otherwise terminate this branch, as this variable is irrelevant to us
            }
        }
    }

    FastTool tool;

    public static void main(String[] args) throws Exception {
        TLCGlobals.warn = false;
        String path = "raft";
        String config = "raft";

        // Avoid sending log messages to stdout and reset the messages recording.
        // TODO unsure if this is needed
        ToolIO.setMode(ToolIO.TOOL);
        ToolIO.reset();

        FastTool tool = new FastTool(path, config);

//        modifyAction(path, tool);
        createAction(tool);
    }

    private static void createAction(FastTool tool) throws IOException {
        TLCState init = tool.getInitStates().elementAt(0);
        List<OpDeclNode> vars = Arrays.asList(init.getVars());
        TLCStateMut goodState = new TLCStateMut(loadValues(vars));

//        OpApplNode node1 = Build.except(Build.op("matchIndex"), Build.stringLiteral("s2"), Build.stringLiteral("hi"));
//        IValue eval = tool.eval(Build.op("matchIndex"), Context.Empty, init);
//        IValue eval1 = tool.eval(node1, Context.Empty, init);

        Enumerate enumerate = new Enumerate(tool, null, null, null);

//        IValue target = jsonToValue(
//                "{\"s1\": {\"type\": \"set\", value: []}," +
//                        "\"s2\": {\"type\": \"set\", value: [\"s2\"]}," +
//                        "\"s3\": {\"type\": \"set\", value: []}" +
//                        "}");
//        target = jsonToValue(
//                "{\"s1\": 0," +
//                        "\"s2\": 1," +
//                        "\"s3\": 0" +
//                        "}");
        IValue target = jsonToValue("1");
        // TODO record indexing
        // TODO embed the whole thing in an except
        // TODO allow specifying what to eval from here
        // TODO cutoff, say number of candidates

        Map<String, ExprOrOpArgNode> seed =
                Arrays.stream(goodState.getVarsAsStrings())
                        .collect(Collectors.toMap(s -> s, s -> Build.op(s)));

        Enumerate.Control synthesized = enumerate.synthesizeStateless(seed, c -> {
            IValue v = tool.eval(c.term, Context.Empty, goodState);
            if (Eval.valueEq(v, target)) {
                c.stop();
            }
        });
        System.out.println(synthesized.term);

        int a = 1;

//        tool.obsEnabled = true;
//
//        // this records evaluated expressions as a side effect
//        StateVec ignored = tool.getNextStates(timeoutWithSomeArgs, goodState);
//
//        tool.obsEnabled = false;

//        IValue eval = tool.eval(any.pred, ref);
//        FormalParamNode r = (FormalParamNode) ref.getName();
//        Context ctx = new Context(null, null, null);
//        FormalParamNode formalParamNode = new FormalParamNode("i", 0,
//                ref.getName().stn, null, r.moduleNode);

        System.out.println("---");
        System.out.println("printing observations");
        tool.observed.entrySet().forEach(e -> {
            System.out.printf("%s: %s\n", e.getValue().term.getOperator().getName(), e.getValue().value);
//            System.out.println("eval");
//            super(1, SyntaxTreeNode.nullSTN, UniqueString.uniqueStringOf(name));
//            SymbolNode name = new OpDefNode(UniqueString.uniqueStringOf("xlog"));
//            System.out.println(name.getName() + " is defined");
//            0, SyntaxTreeNode.nullSTN,
            tool.eval(e.getValue().term, e.getValue().ctx, goodState);
//            tool.eval(e.getValue().term, Context.Empty.cons(name, e.getValue().term), newState);
        });
        System.out.println("---");

//        Eval eval = new Eval();
//
//        Enumerate enumerate = new Enumerate(tool, tool.observed, timeoutWithSomeArgs.con, goodState);
//
////        IValue target = jsonToValue("[s1 |-> {}, s2 |-> {\"s2\"}, s3 |-> {}]", 0);
//        IValue target = jsonToValue(
//                "{\"s1\": {\"type\": \"set\", value: []}," +
//                        "\"s2\": {\"type\": \"set\", value: [\"s2\"]}," +
//                        "\"s3\": {\"type\": \"set\", value: []}" +
//                        "}");
//        OpApplNode answer = enumerate.synthesize(target);
//
//        eval.modify(timeoutWithSomeArgs.pred, timeoutWithSomeArgs.con, goodState);
//
//        try (NamedInputStream stream = new NamedInputStream(path, "raft", new File(path + ".tla"))) {
//            ;
//            TLAplusParser parseTree = new TLAplusParser(stream);
//            System.out.println(parseTree.parse());
//        }

    }

    private static void modifyAction(String path, FastTool tool) throws IOException {
        List<Action> actions = Arrays.asList(tool.getActions());
        List<Action> collect = actions.stream().filter(a -> {
            return a.getName().equals("Timeout");
//            return a.getName().equals("RequestVote");
        }).collect(Collectors.toList());
        Action timeoutWithSomeArgs = collect.get(0);

        // modify the context to inject the values we want
        timeoutWithSomeArgs.con.find("i").setValue(new StringValue("s2"));

        TLCState init = tool.getInitStates().elementAt(0);
        List<OpDeclNode> vars = Arrays.asList(init.getVars());
        TLCStateMut goodState = new TLCStateMut(loadValues(vars));

        tool.obsEnabled = true;

        // this records evaluated expressions as a side effect
        StateVec ignored = tool.getNextStates(timeoutWithSomeArgs, goodState);

        tool.obsEnabled = false;

//        IValue eval = tool.eval(any.pred, ref);
//        FormalParamNode r = (FormalParamNode) ref.getName();
//        Context ctx = new Context(null, null, null);
//        FormalParamNode formalParamNode = new FormalParamNode("i", 0,
//                ref.getName().stn, null, r.moduleNode);

        System.out.println("---");
        System.out.println("printing observations");
        tool.observed.entrySet().forEach(e -> {
            System.out.printf("%s: %s\n", e.getValue().term.getOperator().getName(), e.getValue().value);
//            System.out.println("eval");
//            super(1, SyntaxTreeNode.nullSTN, UniqueString.uniqueStringOf(name));
//            SymbolNode name = new OpDefNode(UniqueString.uniqueStringOf("xlog"));
//            System.out.println(name.getName() + " is defined");
//            0, SyntaxTreeNode.nullSTN,
            tool.eval(e.getValue().term, e.getValue().ctx, goodState);
//            tool.eval(e.getValue().term, Context.Empty.cons(name, e.getValue().term), newState);
        });
        System.out.println("---");

        Eval eval = new Eval();

        Enumerate enumerate = new Enumerate(tool, tool.observed, timeoutWithSomeArgs.con, goodState);

//        IValue target = jsonToValue("[s1 |-> {}, s2 |-> {\"s2\"}, s3 |-> {}]", 0);
        IValue target = jsonToValue(
                "{\"s1\": {\"type\": \"set\", value: []}," +
                        "\"s2\": {\"type\": \"set\", value: [\"s2\"]}," +
                        "\"s3\": {\"type\": \"set\", value: []}" +
                        "}");
//        OpApplNode answer = enumerate.synthesize(target);

        eval.modify(timeoutWithSomeArgs.pred, timeoutWithSomeArgs.con, goodState);

        try (NamedInputStream stream = new NamedInputStream(path, "raft", new File(path + ".tla"))) {
            ;
            TLAplusParser parseTree = new TLAplusParser(stream);
            System.out.println(parseTree.parse());
        }
    }

    private static String goodStateStr = "{\n" +
            "    \"actions\": [],\n" +
            "    \"commitIndex\": {\n" +
            "        \"s1\": 0,\n" +
            "        \"s2\": 0,\n" +
            "        \"s3\": 0\n" +
            "    },\n" +
            "    \"currentTerm\": {\n" +
            "        \"s1\": 1,\n" +
            "        \"s2\": 1,\n" +
            "        \"s3\": 1\n" +
            "    },\n" +
            "    \"inbox\": {\n" +
            "        \"s1\": [],\n" +
            "        \"s2\": [],\n" +
            "        \"s3\": []\n" +
            "    },\n" +
            "    \"inflight\": [],\n" +
            "    \"log\": {\n" +
            "        \"s1\": [],\n" +
            "        \"s2\": [],\n" +
            "        \"s3\": []\n" +
            "    },\n" +
            "    \"matchIndex\": {\n" +
            "        \"s1\": {\n" +
            "            \"s1\": 0,\n" +
            "            \"s2\": 0,\n" +
            "            \"s3\": 0\n" +
            "        },\n" +
            "        \"s2\": {\n" +
            "            \"s1\": 0,\n" +
            "            \"s2\": 0,\n" +
            "            \"s3\": 0\n" +
            "        },\n" +
            "        \"s3\": {\n" +
            "            \"s1\": 0,\n" +
            "            \"s2\": 0,\n" +
            "            \"s3\": 0\n" +
            "        }\n" +
            "    },\n" +
            "    \"nextIndex\": {\n" +
            "        \"s1\": {\n" +
            "            \"s1\": 1,\n" +
            "            \"s2\": 1,\n" +
            "            \"s3\": 1\n" +
            "        },\n" +
            "        \"s2\": {\n" +
            "            \"s1\": 1,\n" +
            "            \"s2\": 1,\n" +
            "            \"s3\": 1\n" +
            "        },\n" +
            "        \"s3\": {\n" +
            "            \"s1\": 1,\n" +
            "            \"s2\": 1,\n" +
            "            \"s3\": 1\n" +
            "        }\n" +
            "    },\n" +
            "    \"outbox\": {\n" +
            "        \"s1\": [],\n" +
            "        \"s2\": [],\n" +
            "        \"s3\": []\n" +
            "    },\n" +
            "    \"state\": {\n" +
            "        \"s1\": \"Follower\",\n" +
            "        \"s2\": \"Follower\",\n" +
            "        \"s3\": \"Follower\"\n" +
            "    },\n" +
            "    \"votedFor\": {\n" +
            "        \"s1\": \"none\",\n" +
            "        \"s2\": \"none\",\n" +
            "        \"s3\": \"none\"\n" +
            "    },\n" +
            "    \"votesGranted\": {\n" +
            "        \"s1\": {\n" +
            "            \"type\": \"set\",\n" +
            "            \"value\": []\n" +
            "        },\n" +
            "        \"s2\": {\n" +
            "            \"type\": \"set\",\n" +
            "            \"value\": []\n" +
            "        },\n" +
            "        \"s3\": {\n" +
            "            \"type\": \"set\",\n" +
            "            \"value\": []\n" +
            "        }\n" +
            "    },\n" +
            "    \"votesResponded\": {\n" +
            "        \"s1\": {\n" +
            "            \"type\": \"set\",\n" +
            "            \"value\": []\n" +
            "        },\n" +
            "        \"s2\": {\n" +
            "            \"type\": \"set\",\n" +
            "            \"value\": []\n" +
            "        },\n" +
            "        \"s3\": {\n" +
            "            \"type\": \"set\",\n" +
            "            \"value\": []\n" +
            "        }\n" +
            "    },\n" +
            "    \"who\": \"none\"\n" +
            "}";

    private static IValue[] loadValues(List<OpDeclNode> vars) {
        JsonObject node = JsonParser.parseString(goodStateStr).getAsJsonObject();

        return vars.stream().map(v -> {
//            return init.getVals().get(v.getName());
            try {
                return Json.getValue(node.get(v.getName().toString()));
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }).toArray(IValue[]::new);
    }

    private static IValue jsonToValue(String s) {
        try {
            return Json.getValue(JsonParser.parseString(s));
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}