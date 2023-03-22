package tlc2.mbtc;

import tlc2.value.impl.Value;

import java.util.Map;

/**
 * An observed state is a state augmented with concrete info about where we saw it
 */
public class ObState {
    String who;
    String label;
    String file;
    int line;
    Map<String, Integer> clock;
    Map<String, Value> data;

    public State toState() {
        return new State(data);
    }
}
