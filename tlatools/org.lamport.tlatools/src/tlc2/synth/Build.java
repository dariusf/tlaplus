package tlc2.synth;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.*;
import tlc2.tool.impl.FastTool;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.StringValue;
import util.UniqueString;

import java.util.ArrayList;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;

import static tla2sany.semantic.ASTConstants.*;

/**
 * AST builder for TLA+ expressions
 */
public class Build {

    public static OpApplNode except(OpApplNode map, ExprOrOpArgNode key, ExprOrOpArgNode value) {
        return Build.op("$Except", map, Build.op("$Pair", Build.op("$Seq", key), value));
    }

    public static OpApplNode op(UniqueString op, ExprOrOpArgNode... args) {
        OpDefNode def = new OpDefNode(op);
        OpApplNode app = new OpApplNode(def);
        // TODO level checking
        app.levelChecked = 1; // disable some errors on new expressions
        // TODO forall params
        // TODO binder params
        app.setArgs(args);
        return app;
    }

    public static OpApplNode op(String op, ExprOrOpArgNode... args) {
        return op(UniqueString.uniqueStringOf(op), args);
    }

    public static StringNode stringLiteral(String s) {
        StringNode str2 = new StringNode(new SyntaxTreeNode(UniqueString.of(s)), false);
        str2.setToolObject(0, new StringValue(s));
        return str2;
    }

    public static NumeralNode number(int num) {
        try {
            NumeralNode n = new NumeralNode(num + "", SyntaxTreeNode.nullSTN);
            n.setToolObject(0, IntValue.gen(num));
            return n;
        } catch (AbortException e) {
            throw new RuntimeException(e);
        }
    }

    public static OpApplNode record(ExprOrOpArgNode... args) {
        List<OpApplNode> pairs = new ArrayList<>();
        for (int i = 0; i < args.length; i += 2) {
            pairs.add(op("$Pair", args[i], args[i + 1]));
        }
        return op(OP_rc, pairs.toArray(OpApplNode[]::new));
    }

    public static OpApplNode setLiteral(ExprOrOpArgNode... args) {
        return op(OP_se, args);
    }

    public static OpApplNode seq(ExprOrOpArgNode... args) {
        return op(OP_tup, args);
    }

    public static OpApplNode fnApp(ExprOrOpArgNode f, ExprOrOpArgNode x) {
        return op(OP_fa, f, x);
    }

    public static BiFunction<ExprOrOpArgNode, ExprOrOpArgNode, OpApplNode> libraryOp(FastTool tool, String mod, String fn) {
        return (left, right) -> {
            OpDefNode appendDef = (OpDefNode) tool.getModule(mod).getDefinitions().stream()
                    .filter(op -> op instanceof OpDefNode && ((OpDefNode) op).getName().equals(fn))
                    .findAny().get();
            return new OpApplNode(appendDef,
                    new ExprOrOpArgNode[]{left, right});
        };
    }

    static <A, B> Function<List<A>, B> unary(Function<A, B> f) {
        return xs -> f.apply(xs.get(0));
    }

    static <A, B> Function<List<A>, B> binary(BiFunction<A, A, B> f) {
        return xs -> f.apply(xs.get(0), xs.get(1));
    }
}
