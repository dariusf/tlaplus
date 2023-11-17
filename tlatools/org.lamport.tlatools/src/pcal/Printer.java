package pcal;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.Vector;
import java.util.stream.Collectors;

public class Printer {
    public static void print(int indent, AST p) {
        System.out.println(show(indent, p));
    }

    public static String show(TLAExpr p) {
        return ((Vector<Vector<TLAToken>>) p.tokens).stream()
                .map(t -> t.stream().map(t1 -> {
                    // TODO could compact further if there are e.g. operator chars
                    if (t1.type == TLAToken.STRING) {
                        return String.format("\"%s\"", t1.string);
                    } else {
                        return t1.string;
                    }
                }).collect(Collectors.joining(" "))) // for each symbol
                .collect(Collectors.joining(" ")); // each line
    }

    // PlusCal statements are printed with no trailing newline
    // Expressions are TLAExprs
    public static String show(int indent, AST p) {
        List<String> result = new ArrayList<>();
        if (p.lbl != null && !p.lbl.isEmpty()) {
            result.add("%s:".formatted(p.lbl));
        }
        if (p instanceof AST.Process) {
            AST.Process p1 = (AST.Process) p;
            String decls = p1.decls.isEmpty() ? "" :
                    ("\n" + indentStr(1, "variables") + "\n" +
                            indentLines(2, ((Vector<AST.VarDecl>) p1.decls).stream()
                                    .map(d -> String.format("%s %s %s;", d.var, d.isEq ? "=" : "in", show(d.val)))
                                    .collect(Collectors.toList())));
            String body = ((Vector<AST>) p1.body).stream()
                    .map(b -> show(1, (AST) b))
                    .collect(Collectors.joining(";\n"));
            result.add(String.format("process (%s %s %s)%s\n{\n%s\n}",
                    p1.name, p1.isEq ? "=" : "\\in", show(p1.id), decls, body));
        } else if (p instanceof AST.Assign) {
            Vector<AST.SingleAssign> ass = ((AST.Assign) p).ass;
            ass.forEach(a -> result.add(String.format("%s := %s;", a.lhs.var, show(a.rhs))));
        } else if (p instanceof AST.When) {
            result.add(String.format("await %s;", show(((AST.When) p).exp)));
        } else if (p instanceof AST.All) {
            AST.All p1 = (AST.All) p;
            result.add(String.format("all (%s %s %s) {", p1.var, p1.isEq ? "=" : "\\in", show(p1.exp)));
            ((Vector<AST>) p1.Do).forEach(b -> result.add(show(1, b)));
            result.add("}");
        } else if (p instanceof AST.Skip) {
            result.add("skip;");
        } else if (p instanceof AST.MacroCall) {
            result.add(String.format("%s(%s)",
                    ((AST.MacroCall) p).name,
                    ((AST.MacroCall) p).args.stream()
                            .map(a -> show((TLAExpr) a))
                            .collect(Collectors.joining(", "))));
        } else {
            throw new RuntimeException("unhandled print case " + p.getClass().getSimpleName());
        }
        return indentLines(indent, result);
    }

    // n is the number of s to generate
    public static String spaces(int n, String s) {
        if (n == 0) {
            return "";
        }
        return new StringBuilder().repeat(s, n).toString();
    }

    // n is the indentation level. the concrete amount of indentation is determined by this function
    public static String indentStr(int n, String s) {
        return spaces(n * 2, " ") + s;
    }

    public static String indentLines(int indent, List<String> result) {
        return result.stream().map(l -> indentStr(indent, l)).collect(Collectors.joining("\n"));
    }
}
