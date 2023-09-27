package tlc2.mbtc;

import tla2sany.semantic.OpApplNode;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

public class StaticAction {
    // parallel lists for existential quantifiers
    List<String> vars;
    List<OpApplNode> sets;
    // formula
    OpApplNode body;

    public StaticAction() {
        this.vars = new ArrayList<>();
        this.sets = new ArrayList<>();
    }
}
