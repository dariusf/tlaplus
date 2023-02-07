package tlc2.monitor;

import tla2sany.semantic.*;
import tlc2.synth.Visitor;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;

import java.util.Arrays;

public class TLDefVisitor extends Visitor<Boolean> {
    @Override
    public Boolean visit(NumeralNode node) {
        return false;
    }

    @Override
    public Boolean visit(StringNode node) {
        return false;
    }

    @Override
    public Boolean visit(OpApplNode node) {
        if (node.getOperator().getName().toString().equals("LogAction")) {
            return true;
        }
        return Arrays.stream(node.getArgs()).anyMatch(a -> a.accept(this));
    }

    @Override
    public Boolean visit(OpArgNode node) {
        return false;
    }

    @Override
    public Boolean visit(LetInNode node) {
        return node.getBody().accept(this);
    }

    @Override
    public Boolean visit(ExprOrOpArgNode node) {
        return false;
    }

    @Override
    public Boolean visit(IntValue intValue) {
        return false;
    }

    @Override
    public Boolean visit(RecordValue recordValue) {
        return false;
    }

    @Override
    public Boolean visit(StringValue stringValue) {
        return false;
    }
}
