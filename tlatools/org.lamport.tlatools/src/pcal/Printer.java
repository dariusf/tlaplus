package pcal;

import java.util.ArrayList;
import java.util.List;
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
                }).collect(Collectors.joining(" "))) // each symbol
                .collect(Collectors.joining(" ")); // each line
    }

    // PlusCal statements are printed with no trailing newline
    // Expressions are TLAExprs
    public static String show(int indent, AST p) {
        List<String> result = new ArrayList<>();
        if (p.lbl != null) {
            result.add("%s:".formatted(p.lbl));
        }
        if (p instanceof AST.Process) {
            AST.Process p1 = (AST.Process) p;
            String decls = p1.decls.isEmpty() ? "" :
                    "\n  variables\n" + indentLines(4, ((Vector<AST.VarDecl>) p1.decls).stream()
                    .map(d -> String.format("%s %s %s;", d.var, d.isEq ? "=" : "in", show(d.val)))
                    .collect(Collectors.toList()));
            String body = ((Vector<AST>) p1.body).stream()
                    .map(b -> show(indent + 2, (AST) b))
                    .collect(Collectors.joining(";\n"));
            result.add(String.format("process (%s \\in %s)%s\n{\n%s\n}",
                    p1.name, show(p1.id), decls, body));
        } else if (p instanceof AST.Assign) {
            Vector<AST.SingleAssign> ass = ((AST.Assign) p).ass;
            ass.forEach(a -> result.add(String.format("%s := %s", a.lhs.var, show(a.rhs))));
        } else if (p instanceof AST.When) {
            result.add(String.format("await %s", show(((AST.When) p).exp)));
//        } else if (p instanceof AST.LabeledStmt) {
//            AST.LabeledStmt p1 = (AST.LabeledStmt) p;
//            result.add(p1.label + ":");
//            ((Vector<AST>) p1.stmts).forEach(s -> result.add(show(indent + 2, s)));
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

    public static String repeat(int n, String s) {
        return new StringBuilder().repeat(s, n).toString();
    }

    public static String indentLines(int indent, List<String> result) {
        return result.stream().map(l -> repeat(indent, " ") + l).collect(Collectors.joining("\n"));
    }
}
