package tlc2.monitor;

import tla2sany.semantic.*;
import util.UniqueString;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

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

    public static RuntimeException fail(String s) {
        RuntimeException e = new RuntimeException(s);
        e.printStackTrace();
        return e;
    }

}
