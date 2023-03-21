package tlc2.mbtc;

import tlc2.value.impl.TupleValue;

import java.util.Set;

public class RankedState {
    State state;
    Set<String> changedFields;
    State proj;
    int score;

    public RankedState(State state, Set<String> changedFields, State proj, int score) {
        this.state = state;
        this.changedFields = changedFields;
        this.proj = proj;
        this.score = score;
    }

    @Override
    public String toString() {
        return String.format("%s %s %d",
                ((TupleValue) state.data.get("actions")).getLast(),
                state.data.get("who"), score);
    }
}
