package pcal;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;
import java.util.stream.Collectors;

public class Printer {
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

    public static String show(AST p) {
        return showLines(0, p).stream().collect(Collectors.joining("\n"));
    }

    // PlusCal statements are printed with no trailing newline
    // Expressions are TLAExprs
    private static List<String> showLines(int indent, AST p) {
        List<String> result = new ArrayList<>();
        if (p.lbl != null && !p.lbl.isEmpty()) {
            result.add("%s:".formatted(p.lbl));
        }
        if (p instanceof AST.Process) {
            AST.Process p1 = (AST.Process) p;
            result.add(String.format("process (%s %s %s)",
                    p1.name, p1.isEq ? "=" : "\\in", show(p1.id)));
            if (!p1.decls.isEmpty()) {
                result.add(indentStr(1, "variables"));
                result.addAll(indentLines(2, ((Vector<AST.VarDecl>) p1.decls).stream()
                        .map(d -> String.format("%s %s %s;", d.var, d.isEq ? "=" : "in", show(d.val)))
                        .collect(Collectors.toList())));
            }
            result.add("{");
            ((Vector<AST>) p1.body).stream()
                    .flatMap(b -> showLines(1, (AST) b).stream())
                    .forEach(b -> result.add(b));
            result.add("}");
        } else if (p instanceof AST.Assign) {
            Vector<AST.SingleAssign> ass = ((AST.Assign) p).ass;
            ass.forEach(a -> result.add(String.format("%s := %s;", a.lhs.var, show(a.rhs))));
        } else if (p instanceof AST.When) {
            result.add(String.format("await %s;", show(((AST.When) p).exp)));
        } else if (p instanceof AST.All) {
            AST.All p1 = (AST.All) p;
            result.add(String.format("all (%s %s %s) {", p1.var, p1.isEq ? "=" : "\\in", show(p1.exp)));
            ((Vector<AST>) p1.Do).forEach(b -> result.addAll(showLines(1, b)));
            result.add("}");
        } else if (p instanceof AST.Clause) {
            AST.Clause p1 = (AST.Clause) p;
            Vector<AST> stmts = p1.unlabOr != null && !p1.unlabOr.isEmpty() ? p1.unlabOr : p1.labOr;
            stmts.forEach(s -> result.addAll(showLines(0, s)));
        } else if (p instanceof AST.Par) {
            AST.Par p1 = (AST.Par) p;
            result.add("par {");
            result.addAll(showLines(1, ((Vector<AST>) p1.clauses).get(0)));
            result.add("} and {");
            result.addAll(showLines(1, ((Vector<AST>) p1.clauses).get(1)));
            result.add("}");
        } else if (p instanceof AST.LabelIf) {
            AST.LabelIf p1 = (AST.LabelIf) p;
            result.add(String.format("if (%s) {", show(p1.test)));
            ((Vector<AST>) p1.unlabThen).forEach(b -> result.addAll(showLines(1, b)));
            result.add("} else {");
            ((Vector<AST>) p1.unlabElse).forEach(b -> result.addAll(showLines(1, b)));
            result.add("}");
        } else if (p instanceof AST.While) {
            AST.While p1 = (AST.While) p;
            result.add(String.format("while (%s)%s {",
                    show(p1.test),
                    p1.extraTests.isEmpty() ? "" : ", " + p1.extraTests.stream()
                            .map(e -> show(e))
                            .collect(Collectors.joining(", "))));
            ((Vector<AST>) p1.labDo).forEach(b -> result.addAll(showLines(1, b)));
            ((Vector<AST>) p1.unlabDo).forEach(b -> result.addAll(showLines(1, b)));
            result.add("}");
        } else if (p instanceof AST.Task) {
            AST.Task p1 = (AST.Task) p;
            result.add(String.format("task %s, %s {", show(p1.partyId), p1.taskId));
            ((Vector<AST>) p1.Do).forEach(s -> result.addAll(showLines(1, s)));
            result.add("}");
        } else if (p instanceof AST.Skip) {
            result.add("skip;");
        } else if (p instanceof AST.Cancel) {
            result.add(String.format("cancel %s;", ((AST.Cancel) p).task));
        } else if (p instanceof AST.MacroCall) {
            AST.MacroCall p1 = (AST.MacroCall) p;
            result.add(String.format("%s(%s);",
                    p1.name,
                    p1.args.stream()
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

//    public static String indentLines(int indent, List<String> result) {
//        return result.stream().map(l -> indentStr(indent, l)).collect(Collectors.joining("\n"));
//    }

    public static List<String> indentLines(int indent, List<String> result) {
        return result.stream().map(l -> indentStr(indent, l)).collect(Collectors.toList());
    }
}
