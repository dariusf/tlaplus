package tlc2.synth;

import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.StringNode;

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

    // for all cases which don't something more specific implemented
    public A visit(ExprOrOpArgNode node) {
        throw new UnsupportedOperationException("unimplemented");
    }
}
