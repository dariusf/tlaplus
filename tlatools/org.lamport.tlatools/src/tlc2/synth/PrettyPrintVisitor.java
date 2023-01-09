package tlc2.synth;

import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.StringNode;

import java.util.Arrays;
import java.util.stream.Collectors;

import static tla2sany.semantic.ASTConstants.*;

/**
 * There is already {@link tlc2.pprint.Format} but that only works for values
 */
public class PrettyPrintVisitor extends Visitor<String> {

    @Override
    public String visit(NumeralNode node) {
        if (node.bigVal() == null) {
            return Integer.toString(node.val());
        } else {
            return node.bigVal().toString();
        }
    }

    @Override
    public String visit(StringNode node) {
        return String.format("\"%s\"", node.getRep());
    }

    @Override
    public String visit(OpApplNode node) {
        String op = node.getOperator().getName().toString();

        if (op.equals(OP_fa.toString())) {
            return String.format("%s[%s]",
                    node.getArgs()[0].accept(this),
                    node.getArgs()[1].accept(this));
            //    } else if (op.equals(OP_seq.toString())) {
            // is OP_seq right?
        } else if (op.equals(OP_tup.toString())) {
            return String.format("<<%s>>",
                    Arrays.stream(node.getArgs())
                            .map(n -> n.accept(this))
                            .collect(Collectors.joining(", ")));
        } else if (op.equals(OP_se.toString())) {
            return String.format("{%s}",
                    Arrays.stream(node.getArgs())
                            .map(n -> n.accept(this))
                            .collect(Collectors.joining(", ")));
        } else if (op.equals(OP_rc.toString())) {
            return String.format("[%s]",
                    Arrays.stream(node.getArgs())
                            .map(a -> {
                                var key = ((OpApplNode) a).getArgs()[0];
                                var val = ((OpApplNode) a).getArgs()[1];
                                return String.format("%s |-> %s", key.accept(this), val.accept(this));
                            })
                            .collect(Collectors.joining(", ")));
        } else if (op.equals(OP_cl.toString())) {
            return String.format("(%s /\\ %s)",
                    node.getArgs()[0].accept(this),
                    node.getArgs()[1].accept(this));
        } else if (op.equals(OP_dl.toString())) {
            return String.format("(%s \\/ %s)",
                    node.getArgs()[0].accept(this),
                    node.getArgs()[1].accept(this));
        } else if (op.equals(OP_exc.toString())) {
            // an $Except has two args, a variable, and a $Pair, whose args are the key and value to assign
            OpApplNode pair = (OpApplNode) node.getArgs()[1];
            ExprOrOpArgNode idx;
//            if (pair.getArgs()[0] instanceof OpApplNode) {
                // in [a EXCEPT ![i] = ...], the i is wrapped in a singleton $Seq OpApplNode
                idx = ((OpApplNode) pair.getArgs()[0]).getArgs()[0];
//            } else {
//                // a string key
//                idx = pair.getArgs()[0];
//            }
            ExprOrOpArgNode exp = pair.getArgs()[1];
            return String.format("[%s EXCEPT ![%s] = %s]",
                    node.getArgs()[0].accept(this),
                    idx.accept(this),
                    exp.accept(this));
        }

        char first = op.charAt(0);
        if (!(first >= 'a' && first <= 'z') && !(first >= 'A' && first <= 'Z') && node.getArgs().length == 2) {
            return String.format("%s %s %s", node.getArgs()[0].accept(this), op, node.getArgs()[1].accept(this));
        }
        if (op.charAt(0) == '$') {
            throw new UnsupportedOperationException("case unimplemented: " + op);
        }
        String args = Arrays.stream(node.getArgs()).map(n -> n.accept(this))
                .collect(Collectors.joining(", "));
        if (node.getArgs().length > 0) {
            args = String.format("(%s)", args);
        }
        return String.format("%s%s", op, args);
    }
}
