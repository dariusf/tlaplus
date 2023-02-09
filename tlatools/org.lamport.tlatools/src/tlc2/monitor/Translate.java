package tlc2.monitor;

import tla2sany.semantic.*;
import util.UniqueString;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.IntStream;

public class Translate {

    enum Type {
        INT,
        RECORD,
        SEQ,
        SET,
        STRING,
        BOOL,
    }

    static int n = 0;

    static String fresh() {
        return String.format("v%d", n++);
    }

    static String fresh(String suffix) {
        return String.format("v%d_%s", n++, suffix);
    }

    /**
     * Builds TLA+ expressions
     */
    static OpApplNode tla(UniqueString op, ExprOrOpArgNode... args) {
        OpDefNode def = new OpDefNode(op);
        OpApplNode app = new OpApplNode(def);
        // TODO level checking
        app.levelChecked = 1; // disable some errors on new expressions
        // TODO forall params
        // TODO binder params
        app.setArgs(args);
        return app;
    }

    static OpApplNode tla(String op, ExprOrOpArgNode... args) {
        return tla(UniqueString.uniqueStringOf(op), args);
    }

    public static boolean isPrimed(SemanticNode body) {
        return body instanceof OpApplNode && ((OpApplNode) body).getOperator().getName().equals("'");
    }

    public static List<ExprOrOpArgNode> operatorArgs(SemanticNode body) {
        if (!(body instanceof OpApplNode)) {
            throw fail("not an operator");
        }
        return new ArrayList<>(Arrays.asList(((OpApplNode) body).getArgs()));
    }

    public static RuntimeException fail(String s, Object... args) {
        RuntimeException e = new RuntimeException(String.format(s, args));
        e.printStackTrace();
        return e;
    }

    /**
     * If no substitution is performed, guarantees substitute(n, subs) == n
     */
    public static <T extends SemanticNode> T substitute(T node, Map<FormalParamNode, ExprOrOpArgNode> subs) {

        // substitute inside lambda bodies, in case they close over variables
        if (node instanceof OpArgNode) {
            OpArgNode oan = (OpArgNode) node;
            OpArgNode res = (OpArgNode) oan.astCopy();
            OpDefNode def = (OpDefNode) oan.getOp();
            OpDefNode def1 = def.astCopy();
            def1.setBody(substitute(def.getBody(), subs));
            res.setOp(def1);
            return (T) res;
        }

        if (!(node instanceof OpApplNode)) {
            return node;
        }

        OpApplNode body = (OpApplNode) node;

        boolean isVar = body.getArgs().length == 0 && body.getAllParams().size() == 1;
        if (isVar) {
            for (Map.Entry<FormalParamNode, ExprOrOpArgNode> e : subs.entrySet()) {
                // checking size = 1 makes this not "containingBoundVar"
                boolean isBound = body.getAllParams().contains(e.getKey());
                if (isBound) {
                    return (T) e.getValue();
                }
            }
        }

        // not a bound variable. try to substitute inside it
        ExprOrOpArgNode[] args = Arrays.stream(body.getArgs())
                .map(a -> {
//                    for (Map.Entry<FormalParamNode, OpApplNode> e : subs.entrySet()) {
//                        // checking size = 1 makes this not "containingBoundVar"
//                        boolean isBoundVar = a.getAllParams().contains(e.getKey()) && a.getAllParams().size() == 1;
//                        if (isBoundVar) {
//                            return e.getValue();
//                        }
//                    }
                    if (a instanceof OpApplNode || a instanceof OpArgNode) {
                        return substitute(a, subs);
                    }
                    return a;
                })
                .toArray(ExprOrOpArgNode[]::new);

        boolean unchanged = IntStream.range(0, args.length).allMatch(i -> args[i] == body.getArgs()[i]);
        if (unchanged) {
            return node;
        }

        OpApplNode res = body.astCopy();
        res.setArgs(args);
        // System.out.printf("sub %s => %s%n", Eval.prettyPrint(body), Eval.prettyPrint(res));

        // this is essentially (OpApplNode) res and is safe due to the checks above
        return (T) res;
    }

}
