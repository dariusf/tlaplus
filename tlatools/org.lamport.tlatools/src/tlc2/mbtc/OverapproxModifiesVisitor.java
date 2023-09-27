package tlc2.mbtc;

import tla2sany.semantic.*;
import tlc2.synth.Visitor;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.ToolGlobals;
import tlc2.tool.impl.FastTool;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import util.UniqueString;

import java.util.*;
import java.util.stream.Collectors;

import static tlc2.tool.ToolGlobals.*;

public class OverapproxModifiesVisitor extends Visitor<OverapproxModifiesVisitor.R> {

    public static class R {

        Set<String> may;
        Set<String> must;

        public R() {
            may = new HashSet<>();
            must = new HashSet<>();
        }

        public R(R r) {
                    may = r.may;
                    must = r.must;
        }
    }

    private final FastTool tool;

    public OverapproxModifiesVisitor(FastTool tool) {
        this.tool = tool;
    }

    Optional<String> primedVarName(ExprOrOpArgNode node) {
        if (!(node instanceof OpApplNode)) {
            return Optional.empty();
        }
        OpApplNode op = (OpApplNode) node;
        int opCode = BuiltInOPs.getOpCode(op.getOperator().getName());
        if (opCode == ToolGlobals.OPCODE_prime) {
            ExprOrOpArgNode v = op.getArgs()[0];
            if (v instanceof OpApplNode) {
                return Optional.of(((OpApplNode) v).getOperator().getName().toString());
            }
        }
        return Optional.empty();
    }

    @Override
    public R visit(OpApplNode node) {
        UniqueString opName = node.getOperator().getName();
        int opCode = BuiltInOPs.getOpCode(opName);
        if (opCode == OPCODE_cl || opCode == OPCODE_dl) {
            List<R> args = Arrays.stream(node.getArgs()).map(n -> n.accept(this)).collect(Collectors.toList());
//            S left = node.getArgs()[0].accept(this);
//            S right = node.getArgs()[1].accept(this);
            if (opCode == OPCODE_cl) {
                // union all sets
                R res = new R();
                args.forEach(a -> {
                res.may.addAll(a.may);
                res.must.addAll(a.must);
                });
                return res;
            } else {
                // must has to be in both branches, everything else is may
                R res = new R(args.get(0));
                args.forEach(a -> {
                    // symmetric difference
                    Set<String> diff1 = new HashSet<>(res.must);
                    diff1.removeAll(a.must);
                    Set<String> diff2 = new HashSet<>(a.must);
                    diff2.removeAll(res.must);
                    res.may.addAll(diff1);
                    res.may.addAll(diff2);
                    res.may.addAll(a.may);

                    // intersection
                    res.must.retainAll(a.must);
                });
                return res;
            }
        }
        // we are dealing with a prop
        // assume every primed variable appears directly under an eq (no in)
        if (opCode == OPCODE_eq) {
            ExprOrOpArgNode left = node.getArgs()[0];
            ExprOrOpArgNode right = node.getArgs()[1];
            Optional<String> n = primedVarName(left);
            if (n.isPresent()) {
                R res = new R();
                res.must.add(n.get());
                return res;
            }
                    n = primedVarName(right);
            if (n.isPresent()) {
                R res = new R();
                res.must.add(n.get());
                return res;
            }

            return new R();
        } else {
            Object def = tool.getSpecProcessor().getDefns().get(opName.toString());
            if (def instanceof OpDefNode) {
                // we're dealing with a user-defined function. recurse on its body
                return ((OpDefNode) def).getBody().accept(this);
            }

            // cannot be analyzed?
            return new R();

//            if (opName.equals("Send")) {
//                // TODO hardcoded for now
//                R res = new R();
//                res.must.add("outbox");
//                return res;
//            } else if (opName.equals("Receive")) {
//                // TODO hardcoded for now
//                R res = new R();
//                res.must.add("inbox");
//                return res;
//            } else if (opName.equals("Reply")) {
//                // TODO hardcoded for now
//                R res = new R();
//                res.must.add("outbox");
//                res.must.add("inbox");
//                return res;
//            } else {
//                int a = 1;
////            System.out.printf("unhandled %s\n", node.getOperator().getName());
//            }
        }
    }

    @Override
    public R visit(LetInNode node) {
        // the bindings can't contribute as they are all pure
        return node.getBody().accept(this);
    }

    @Override
    public R visit(NumeralNode node) {
        return new R();
    }

    @Override
    public R visit(StringNode node) {
        return new R();
    }

    @Override
    public R visit(OpArgNode node) {
        return new R();
    }

    @Override
    public R visit(ExprOrOpArgNode node) {
        return new R();
    }

    @Override
    public R visit(IntValue intValue) {
        return new R();
    }

    @Override
    public R visit(RecordValue recordValue) {
        return new R();
    }

    @Override
    public R visit(StringValue stringValue) {
        return new R();
    }
}
