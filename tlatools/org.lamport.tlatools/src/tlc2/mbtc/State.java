package tlc2.mbtc;

import com.google.gson.TypeAdapter;
import com.google.gson.reflect.TypeToken;
import com.google.gson.stream.JsonReader;
import com.google.gson.stream.JsonWriter;
import tlc2.value.impl.Value;

import java.io.IOException;
import java.lang.reflect.Type;
import java.util.Map;

public class State {
    Map<String, Value> data;

    public State(Map<String, Value> data) {
        this.data = data;
    }

    private static final Type MAP_STRING_VALUE = new TypeToken<Map<String, Value>>() {
    }.getType();

    public static class Deserializer extends TypeAdapter<State> {

        @Override
        public void write(JsonWriter jsonWriter, State state) throws IOException {
            throw new UnsupportedOperationException("not yet implemented");
        }

        @Override
        public State read(JsonReader jsonReader) throws IOException {
            return new State(MBTC.gson.fromJson(jsonReader, MAP_STRING_VALUE));
        }
    }
}
