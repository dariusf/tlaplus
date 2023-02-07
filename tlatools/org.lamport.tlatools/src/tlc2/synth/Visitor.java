package tlc2.synth;

import tla2sany.semantic.*;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;

/**
 * There is already {@link tla2sany.semantic.SemanticNode.ChildrenVisitor},
 * but this is slightly more high-level and gives access to more granular types.
 */
public abstract class Visitor<A> {
    public A visit(NumeralNode node) {
        throw new UnsupportedOperationException("unimplemented");
    }

    public A visit(StringNode node) {
        throw new UnsupportedOperationException("unimplemented");
    }

    public A visit(OpApplNode node) {
        throw new UnsupportedOperationException("unimplemented");
    }

    public A visit(OpArgNode node) {
        throw new UnsupportedOperationException("unimplemented");
    }

    public A visit(LetInNode node) {
        throw new UnsupportedOperationException("unimplemented");
    }

    // for all cases which don't something more specific implemented
    public A visit(ExprOrOpArgNode node) {
        throw new UnsupportedOperationException("unimplemented");
    }

    public A visit(IntValue intValue) {
        throw new UnsupportedOperationException("unimplemented");
    }

    public A visit(RecordValue recordValue) {
        throw new UnsupportedOperationException("unimplemented");
    }

    public A visit(StringValue stringValue) {
        throw new UnsupportedOperationException("unimplemented");
    }
}
