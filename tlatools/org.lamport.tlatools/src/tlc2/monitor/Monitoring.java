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
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.BiFunction;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static tlc2.monitor.Translate.fail;

public class Monitoring {

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

    public static void convert(Defns defns, Map<UniqueString, IValue> initialState, ModuleNode rootModule) throws Exception {

        String overallTemplate = Objects.requireNonNull(getResourceFileAsString("tlc2/MonitorTemplate.go"));

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
            String params = translateParams(d, (i, p) -> String.format("%s any", p.getName().toString()));
            GoTranslation translation = new GoTranslation(defns);
            GoBlock body = translation.translateTopLevel(defns, d.getBody());
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
                        .map(d -> String.format("case %1$s:\nif err := m.Check%1$s(%2$si, prev, this); err != nil {\nreturn err\n}",
                                d.getName().toString(),
                                translateParams(d, (i, p) -> String.format("this.params[%d]", i)))
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
}
