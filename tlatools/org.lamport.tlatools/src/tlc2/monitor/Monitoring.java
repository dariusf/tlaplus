package tlc2.monitor;

import tla2sany.semantic.*;
import tlc2.tool.Defns;
import tlc2.value.IValue;
import util.UniqueString;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.BiFunction;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static tlc2.monitor.GoTranslation.publicVarName;
import static tlc2.monitor.Translate.fail;

public class Monitoring {

    public static Set<String> libraryFunctions = new HashSet<>();

    static {
        libraryFunctions.addAll(List.of(
                "ToSet", "Option", "Some", "None",
                // raft
                "MapThenFoldSet", "FoldFunction", "FoldSeq", "Remove",
                "RemoveAt", "IsPrefix", "IsInjective", "SetToSeq",
                "Min", "Max"
        ));
    }

    static String getResourceFileAsString(String fileName) throws IOException {
        ClassLoader classLoader = ClassLoader.getSystemClassLoader();
        try (InputStream is = classLoader.getResourceAsStream(fileName)) {
            if (is == null) return null;
            try (InputStreamReader isr = new InputStreamReader(is);
                 BufferedReader reader = new BufferedReader(isr)) {
                return reader.lines().collect(Collectors.joining(System.lineSeparator()));
            }
        }
    }

    public static String removeProjected(String name) {
        if (name.endsWith("Projected")) {
            int l = name.length() - "Projected".length();
            return name.substring(0, l);
        }
        return name;
    }

    public static Stream<String> translateDef(OpDefNode d,
                                              Set<String> translatedDefs,
                                              Defns defns,
                                              Map<String, IValue> constants,
                                              Set<String> declaredVariableNames) {
        try {
            if (d.getBody() instanceof SubstInNode) {
                // INSTANCE declarations are one instance of this
                return Stream.of();
            }
//                Set<String> letBoundNames = new HashSet<>();
            // TODO move this into GoTranslation
            GoTranslation translation = new GoTranslation(defns, constants, declaredVariableNames);

            // inline all the let bindings
//                GoBlock letBindings = goBlock("");
//                ExprNode defBody = d.getBody();
//                while (defBody instanceof LetInNode) {
//                    LetInNode let = (LetInNode) defBody;
//                    for (OpDefNode letLet : let.getLets()) {
//                        // TODO assume there are no local operator definitions
//                        String letVar = letLet.getName().toString();
//                        translation.boundVarNames.add(letVar);
//                        letBindings = letBindings.seq(goBlock("var %s TLA = %s",
//                                letVar, translation.translateExpr(letLet.getBody(), null)));
//                    }
//                    defBody = let.getBody();
//                }

//                if (!(defBody instanceof OpApplNode)) {
//                    // TODO let bindings show up BOTH as top-level operator definitions and as LetInNodes.
//                    //  From a quick glance at their state, there doesn't seem to be a way to filter them out.
//                    //  We ignore them as there is code above for inlining them.
//                    String m = String.format("%s is not an OpApplNode but an %s", d.getName(), d.getBody().getClass().getSimpleName());
//                    throw new CannotBeTranslatedException(m);
//                }
            String params = translateParams(d, (i, p) -> String.format("%s TLA", p.getName().toString()))
                    .collect(Collectors.joining(", "));
            if (!params.isEmpty()) {
                params += ", ";
            }

            List<String> paramNames = translateParams(d, (i, p) -> p.getName().toString())
                    .collect(Collectors.toList());

            translation.boundVarNames.addAll(paramNames);
            GoBlock body = translation.translateTopLevel(removeProjected(d.getName().toString()), d.getBody());
            translation.boundVarNames.removeAll(paramNames);

            String a = String.format("func (monitor *Monitor) Check%s(%strace_i int, prev Event, this Event) error {\n" +
                            "%s\n" +
                            "return nil\n" +
                            "}",
                    removeProjected(d.getName().toString()),
                    params,
//                        letBindings.seq(body)
                    body
            );
            translatedDefs.add(d.getName().toString());
            return Stream.of(a);
        } catch (CannotBeTranslatedException e) {
            return Stream.of(String.format("/* Action %s cannot be translated because of: %s */",
                    d.getName(), e.getMessage()));
        }
    }

    public static void translate(Defns defns, Map<String, IValue> constants, Map<UniqueString, IValue> initialState, ModuleNode rootModule) throws Exception {

        String overallTemplate = Objects.requireNonNull(getResourceFileAsString("tlc2/monitor/Monitor.go.template"));

        UniqueString moduleName = rootModule.getName();
        List<OpDeclNode> variables = Arrays.asList(rootModule.getVariableDecls());
        Set<String> declaredVariableNames = variables.stream()
                .map(v -> v.getName().toString())
                .collect(Collectors.toSet());

//        String constantsFields = constants.entrySet().stream()
//                .map(e ->
//                        String.format("%s %s", e.getKey(), "any") // TODO?
//                ).collect(Collectors.joining("\n"));

        List<OpDefNode> definitions = rootModule.getDefinitions().stream()
                // exclude definitions pulled in by an INSTANCE
                .filter(d -> ((OpDefNode) d).getSource().getOriginallyDefinedInModuleNode() == rootModule)
                .filter(Monitoring::operatorWhitelist)
                .map(d -> (OpDefNode) d)
                .collect(Collectors.toList());

        // Add some definitions found in used modules
        definitions.addAll(rootModule.getExtendedModuleSet().stream()
                .filter(m -> m.getName().toString().equals("InboxOutbox"))
                .flatMap(m -> m.getDefinitions().stream()
                        .map(d -> (OpDefNode) d)
                        .filter(d -> d.getName().toString().endsWith("Projected")))
                // .map(d -> ((OpDefNode) d).setBody()))
                .collect(Collectors.toList()));

        TLDefVisitor tldVisitor = new TLDefVisitor();
        Set<String> topLevelDefs = definitions.stream()
                .filter(d -> d.getBody().accept(tldVisitor))
                .map(d -> d.getName().toString())
                .collect(Collectors.toSet());

        if (!topLevelDefs.isEmpty()) {
            definitions = definitions.stream()
                    .filter(d -> topLevelDefs.contains(d.getName().toString()))
                    .collect(Collectors.toList());
        }

        // Definitions which translated successfully, so we don't generate other stuff for the failed ones
        Set<String> translatedDefs = new HashSet<>();

        String monitorFns = definitions.stream()
                .flatMap(d -> translateDef(d, translatedDefs, defns, constants, declaredVariableNames))
                .collect(Collectors.joining("\n\n"));

        GoBlock initialBody;
        {
            GoTranslation translation = new GoTranslation(defns, constants, declaredVariableNames);
            initialBody = translation.translateInitial(initialState);
        }

        String pkg = "monitor";
        String varDecls = declaredVariableNames.stream()
                .map(v -> String.format("%s TLA", publicVarName(v)))
                .collect(Collectors.joining("\n"));

        String actionNames = definitions.stream()
                .filter(d -> translatedDefs.contains(d.getName().toString()))
                .map(d -> d.getName().toString())
                .map(Monitoring::removeProjected)
                .collect(Collectors.joining("\n"));

        String stringSwitchCases = definitions.stream()
                .filter(d -> translatedDefs.contains(d.getName().toString()))
                .map(d -> d.getName().toString())
                .map(Monitoring::removeProjected)
                .map(d -> String.format("case %1$s:\nreturn \"%1$s\"", d))
                .collect(Collectors.joining("\n"));

        String checkSwitchCases = definitions.stream()
                .filter(d -> translatedDefs.contains(d.getName().toString()))
                .map(d -> {
                    String params = translateParams(d, (i, p) -> String.format("this.Params[%d]", i)).collect(Collectors.joining(", "));
                    if (!params.isEmpty()) {
                        params += ", ";
                    }
                    return String.format("case %1$s:\n" +
                                    "if err := m.Check%1$s(%2$si, prev, this); err != nil {\n" +
                                    "return err\n" +
                                    "}",
                            removeProjected(d.getName().toString()),
                            params);
                })
                .collect(Collectors.joining("\n"));

        String varAssignments = declaredVariableNames.stream().map(v ->
                        String.format("if v.State.%1$s != nil {\n" +
                                "c.%1$s = v.State.%1$s\n" +
                                "}", publicVarName(v)))
                .collect(Collectors.joining("\n"));

        String module = String.format(overallTemplate,
                pkg, varDecls, actionNames,
                stringSwitchCases,
//                constantsFields,
                checkSwitchCases, initialBody, monitorFns, varAssignments);
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
    }

    private static Stream<String> translateParams(OpDefNode d, BiFunction<Integer, FormalParamNode, String> f) {
        if (d.getArity() == 0) {
            return Stream.of();
        } else {
            return IntStream.range(0, d.getArity())
                    .mapToObj(i -> f.apply(i, d.getParams()[i]));
        }
    }

    private static boolean operatorWhitelist(SemanticNode d) {
        if (d instanceof OpDefNode) {
            String name = ((OpDefNode) d).getName().toString();
            List<String> extra = List.of("TC", "TCConsistent", "SoupSize", "TargetLength", "TargetA", "ConstrB", "TargetCommit", "TargetAbort");
            if (name.contains("TypeOK") || name.contains("Spec") || name.contains("vars") ||
                    name.contains("Next") || name.endsWith("Init")) {
                // Init is ignored because it's already availale.
                // we should get the actions from Next but we just keep everything left instead.
                return false;
            } else if (extra.contains(name)) {
                // User-defined blacklist
                return false;
            } else if (List.of("Messages", "Receive", "Send").contains(name) || libraryFunctions.contains(name)) {
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
}
