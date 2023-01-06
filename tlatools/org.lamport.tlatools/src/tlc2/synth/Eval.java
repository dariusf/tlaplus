package tlc2.synth;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.jline.reader.EndOfFileException;
import org.jline.reader.LineReader;
import tla2sany.semantic.*;
import tlc2.module.Json;
import tlc2.tool.*;
import org.jline.reader.UserInterruptException;
import tla2sany.parser.TLAplusParser;
import tlc2.tool.impl.FastTool;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;
import util.*;

import java.io.*;
import java.lang.reflect.Method;
import java.nio.file.Path;
import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static tla2sany.semantic.ASTConstants.OpApplKind;
import static tlc2.tool.ToolGlobals.*;

public class Eval {

    private static final String HISTORY_PATH = System.getProperty("user.home", "") + File.separator + ".tlaplus" + File.separator + "history.repl";

    // The spec file to use in the REPL context, if any.
    private File specFile = null;

    // The naming prefix of the temporary directory.
    static final String TEMP_DIR_PREFIX = "tlarepl";

    // The name of the spec used for evaluating expressions.
    final String REPL_SPEC_NAME = "tlarepl";

    private static final String prompt = "(tla+) ";

    private final Writer replWriter = new PrintWriter(System.out);

    // A temporary directory to place auxiliary files needed for REPL evaluation.
    Path replTempDir;

    public Eval(Path tempDir) {
        replTempDir = tempDir;
    }

    public Eval() {
    }

    public void setSpecFile(final File pSpecFile) {
        specFile = pSpecFile;
    }

    /**
     * Evaluate the given string input as a TLA+ expression.
     *
     * @return the pretty printed result of the evaluation or an empty string if there was an error.
     */
    public String processInput(String evalExpr) {

        // The modules we will extend in the REPL environment.
        String moduleExtends = "Reals,Sequences,Bags,FiniteSets,TLC,Randomization";
        try {
            // Try loading the "index" class of the Community Modules that define
            // popular modulesl that should be loaded by default. If the Community Modules
            // are not present, silently fail.
            final Class<?> clazz = Class.forName("tlc2.overrides.CommunityModules");
            final Method m = clazz.getDeclaredMethod("popularModules");
            moduleExtends += String.format(",%s", m.invoke(null));
        } catch (Exception | NoClassDefFoundError ignore) {
        }

        if (specFile != null) {
            String mainModuleName = specFile.getName().replaceFirst(TLAConstants.Files.TLA_EXTENSION + "$", "");
            moduleExtends += ("," + mainModuleName);
        }

        File tempFile, configFile;
        try {

            // We want to place the spec files used by REPL evaluation into the temporary directory.
            tempFile = new File(replTempDir.toString(), REPL_SPEC_NAME + TLAConstants.Files.TLA_EXTENSION);
            configFile = new File(replTempDir.toString(), REPL_SPEC_NAME + TLAConstants.Files.CONFIG_EXTENSION);

            // Create the config file.
            BufferedWriter cfgWriter = new BufferedWriter(new FileWriter(configFile.getAbsolutePath(), false));
            cfgWriter.append("INIT replinit");
            cfgWriter.newLine();
            cfgWriter.append("NEXT replnext");
            cfgWriter.newLine();
            cfgWriter.close();

            // Create the spec file lines.
            ArrayList<String> lines = new ArrayList<String>();
            String replValueVarName = "replvalue";
            lines.add("---- MODULE tlarepl ----");
            lines.add("EXTENDS " + moduleExtends);
            lines.add("VARIABLE replvar");
            // Dummy Init and Next predicates.
            lines.add("replinit == replvar = 0");
            lines.add("replnext == replvar' = 0");
            // The expression to evaluate.
            lines.add(replValueVarName + " == " + evalExpr);
            lines.add("====");

            // Write out the spec file.
            BufferedWriter writer = new BufferedWriter(new FileWriter(tempFile.getAbsolutePath(), false));
            for (String line : lines) {
                writer.append(line);
                writer.newLine();
            }
            writer.close();

            // Avoid sending log messages to stdout and reset the messages recording.
            ToolIO.setMode(ToolIO.TOOL);
            ToolIO.reset();

            try {
                // We placed the REPL spec files into a temporary directory, so, we add this temp directory
                // path to the filename resolver used by the Tool.
                SimpleFilenameToStream resolver = new SimpleFilenameToStream(replTempDir.toAbsolutePath().toString());
                Tool tool = new FastTool(REPL_SPEC_NAME, REPL_SPEC_NAME, resolver);
                ModuleNode module = tool.getSpecProcessor().getRootModule();
                OpDefNode valueNode = module.getOpDef(replValueVarName);

                // Make output of TLC!Print and TLC!PrintT appear in the REPL. Set here
                // and unset in finally below to suppress output of FastTool instantiation
                // above.
                tlc2.module.TLC.OUTPUT = replWriter;
                final Value exprVal = (Value) tool.eval(valueNode.getBody());
                return exprVal.toString();
            } catch (EvalException exc) {
                // TODO: Improve error messages with more specific detail.
                System.out.printf("Error evaluating expression: '%s'%n%s%n", evalExpr, exc);
            } catch (Assert.TLCRuntimeException exc) {
                if (exc.parameters != null && exc.parameters.length > 0) {
                    // 0..1 \X 0..1 has non-null params of length zero. Actual error message is
                    // "Parsing or semantic analysis failed.".
                    System.out.printf("Error evaluating expression: '%s'%n%s%n", evalExpr,
                            Arrays.toString(exc.parameters));
                } else if (exc.getMessage() != null) {
                    // Examples of what ends up here:
                    // 23 = TRUE
                    // Attempted to evaluate an expression of form P \/ Q when P was an integer.
                    // 23 \/ TRUE
                    // Attempted to check equality of integer 23 with non-integer: TRUE
                    // CHOOSE x \in Nat : x = 4
                    // Attempted to compute the value of an expression of form CHOOSE x \in S: P, but S was not enumerable.
                    String msg = exc.getMessage().trim();
                    // Strip meaningless location from error message.
                    msg = msg.replaceFirst("\\nline [0-9]+, col [0-9]+ to line [0-9]+, col [0-9]+ of module tlarepl$", "");
                    // Replace any newlines with whitespaces.
                    msg = msg.replaceAll("\\n", " ").trim();
                    System.out.printf("Error evaluating expression: '%s'%n%s%n", evalExpr, msg);
                } else {
                    System.out.printf("Error evaluating expression: '%s'%n", evalExpr);
                }
            } finally {
                replWriter.flush();
                tlc2.module.TLC.OUTPUT = null;
            }
        } catch (IOException pe) {
            pe.printStackTrace();
        }
        return "";
    }

    /**
     * Runs the main REPL loop continuously until there is a fatal error or a user interrupt.
     */
    public void runREPL(final LineReader reader) throws IOException {
        // Run the loop.
        String expr;
        while (true) {
            try {
                expr = reader.readLine(prompt);
                String res = processInput(expr);
                if (res.equals("")) {
                    continue;
                }
                System.out.println(res);
            } catch (UserInterruptException e) {
                return;
            } catch (EndOfFileException e) {
                e.printStackTrace();
                return;
            } finally {
                // Persistent file and directory will be create on demand.
                reader.getHistory().save();
            }
        }
    }

    OpApplNode append(ExprOrOpArgNode left, ExprOrOpArgNode right) {
        OpDefNode appendDef = (OpDefNode) tool.getModule("Sequences").getDefinitions().stream()
                .filter(op -> op instanceof OpDefNode && ((OpDefNode) op).getName().equals("Append"))
                .findAny().get();
        return new OpApplNode(appendDef,
                new ExprOrOpArgNode[]{left, right});
    }

    OpApplNode setLiteral(ExprOrOpArgNode arg) {
        SymbolNode setLiteral = new OpDefNode(OP_se);
        OpApplNode set = new OpApplNode(setLiteral, new ExprOrOpArgNode[]{arg});
        return set;
    }

    static <A, B> Function<List<A>, B> unary(Function<A, B> f) {
        return xs -> f.apply(xs.get(0));
    }

    static <A, B> Function<List<A>, B> binary(BiFunction<A, A, B> f) {
        return xs -> f.apply(xs.get(0), xs.get(1));
    }

    static <T> Stream<List<T>> cartesianProduct(List<List<T>> lists) {
        if (lists.size() == 0) {
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

    class Enumerate {
        Map<String, Tool.TermVal> components;
        Context ctx;
        TLCState state;

        public Enumerate(Map<String, Tool.TermVal> components, Context ctx, TLCState state) {
            this.components = components;
            this.ctx = ctx;
            this.state = state;
        }

        int rank(OpApplNode left) {
            // balance size and generality
            return 1;
        }

        Stream<List<OpApplNode>> product(int n) {
            List<List<OpApplNode>> components = new ArrayList<>();
            for (int i = 0; i < n; i++) {
                components.add(this.components.values().stream().map(a -> a.term).toList());
            }
            return cartesianProduct(components);
        }

        // compute next frontier
        void next() {
            List<List<Function<List<ExprOrOpArgNode>, OpApplNode>>> rules = List.of(
                    List.of(unary(Eval.this::setLiteral)),
                    List.of(binary(Eval.this::append))
            );
            Map<String, Tool.TermVal> additions = new HashMap<>();
            for (int i = 0; i < rules.size(); i++) {
                final int j = i;
                product(i + 1).forEach(p -> {
                    List<ExprOrOpArgNode> p1 = p.stream()
                            .map(p2 -> (ExprOrOpArgNode) p2)
                            .collect(Collectors.toList());
                    // TODO prune non-promising expressions like {{}}?
                    //  so we don't keep them as components. hard to identify them though
                    rules.get(j).forEach(r -> {
                        OpApplNode candidate = r.apply(p1);
                        try {
                            IValue res = tool.eval(candidate, ctx, state);
                            System.out.printf("%s ==> %s\n", prettyPrint(candidate), res);
                        } catch (EvalException e) {
                            // not sure if it's worth pruning ill-typed expressions because they're
                            // removed in one traversal, by evaluation
                            // System.out.printf("%s =/=>\n", candidate.prettyPrint());
                        }
                    });
                    // TODO check first
                    if (false) {
                        // TODO add expr and result
                        additions.put(null, null);
                    }
                });
            }
            components.putAll(additions);
        }

        OpApplNode done(Value target) {
            if (components.values().stream().anyMatch(v -> v.toString().equals(target.toString()))) {
                return components.get(target.toString()).term;
            }
            return null;
        }
    }

    public static String prettyPrint(ExprOrOpArgNode node) {
        return node.accept(new PrettyPrintVisitor());
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
        String path = "/Users/darius/refinement-mappings/trace-specs/raft-outbox/raft";
        String config = "/Users/darius/refinement-mappings/trace-specs/raft-outbox/raft";

        FastTool tool = new FastTool(path, config);

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
        eval.tool = tool;

        Enumerate enumerate = eval.new Enumerate(tool.observed, timeoutWithSomeArgs.con, goodState);

        enumerate.next();

        eval.modify(timeoutWithSomeArgs.pred, timeoutWithSomeArgs.con, goodState);

        try (NamedInputStream stream = new NamedInputStream(path, "raft", new File(path + ".tla"))) {
            ;
            TLAplusParser parseTree = new TLAplusParser(stream);
            System.out.println(parseTree.parse());
        }

        // Here is the one true REAL call to the parseTree.parse() for a file;
        // The root node of the parse tree is left in parseTree.

//        try {
//            final Path tempDir = Files.createTempDirectory(TEMP_DIR_PREFIX);
//            final Eval repl = new Eval(tempDir);
//            // TODO: Allow external spec file to be loaded into REPL context.
//
//            if(args.length == 1) {
//                String res = repl.processInput(args[0]);
//                if (!res.equals("")) {
//                	System.out.println(res);
//                }
//                //TODO Return actual exit value if parsing/evaluation fails.
//                System.exit(0);
//            }
//
//            // For TLA+ we don't want to treat backslashes as escape chars e.g. for LaTeX like operators.
//			final DefaultParser parser = new DefaultParser();
//			parser.setEscapeChars(null);
//			final Terminal terminal = TerminalBuilder.builder().build();
//			final LineReader reader = LineReaderBuilder.builder().parser(parser).terminal(terminal)
//					.history(new DefaultHistory()).build();
//			reader.setVariable(LineReader.HISTORY_FILE, HISTORY_PATH);
//
//			System.out.println("Welcome to the TLA+ REPL!");
//            MP.printMessage(EC.TLC_VERSION, TLCGlobals.versionOfTLC);
//        	System.out.println("Enter a constant-level TLA+ expression.");
//
//            repl.runREPL(reader);
//        } catch (Exception e) {
//            e.printStackTrace();
//        }
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
}
