package tlc2.monitor;

import tla2sany.semantic.*;
import util.UniqueString;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class Translate {

    enum Type {
        INT
    }

    static int n = 0;

    static String fresh() {
        return "v" + n++;
    }

    /**
     * Builds TLA+ expressions
     */
    static OpApplNode tla(UniqueString op, ExprOrOpArgNode... args) {
        OpDefNode def = new OpDefNode(op);
        OpApplNode app = new OpApplNode(def);
        app.setArgs(args);
        return app;
    }

    static OpApplNode tla(String op, ExprOrOpArgNode... args) {
        return tla(UniqueString.uniqueStringOf(op), args);
    }

    public static boolean isVar(SemanticNode body) {
        return body instanceof OpApplNode && ((OpApplNode) body).getArgs().length == 0;
    }

    public static String getVarName(OpApplNode fml) {
        return fml.getOperator().getName().toString();
    }

    public static boolean isPrimedVar(SemanticNode body) {
        return body instanceof OpApplNode && ((OpApplNode) body).getOperator().getName().equals("'");
    }

    public static boolean isConstant(SemanticNode body) {
        return body instanceof StringNode || body instanceof NumeralNode;
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

    public static OpApplNode substitute(OpApplNode body, Map<FormalParamNode, OpApplNode> subs) {
        ExprOrOpArgNode[] args = Arrays.stream(body.getArgs())
                .map(a -> {
                    for (Map.Entry<FormalParamNode, OpApplNode> e : subs.entrySet()) {
                        if (a.getAllParams().contains(e.getKey())) {
                            return e.getValue();
                        }
                    }
                    if (a instanceof OpApplNode) {
                        return substitute((OpApplNode) a, subs);
                    }
                    return a;
                })
                .toArray(ExprOrOpArgNode[]::new);
        OpApplNode res = new OpApplNode(body.getOperator());
        res.setArgs(args);
        return res;
    }

}
