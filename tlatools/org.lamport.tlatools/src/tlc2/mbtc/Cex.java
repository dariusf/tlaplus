package tlc2.mbtc;

import java.util.List;

public class Cex {
    int prefixI;
    List<State> tracePrefix;
    List<Event> implTrace;
    List<State> frontier;

    State goodState() {
        return tracePrefix.get(tracePrefix.size() - 1);
    }

    Event badState() {
        return implTrace.get(prefixI);
    }
}
