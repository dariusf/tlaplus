package tlc2.mbtc;

import com.google.gson.JsonElement;
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

    public static class Adapter extends TypeAdapter<State> {

        @Override
        public void write(JsonWriter jsonWriter, State state) throws IOException {
            MBTC.gson.toJson(state.data, MAP_STRING_VALUE, jsonWriter);
        }

        @Override
        public State read(JsonReader jsonReader) throws IOException {
            return new State(MBTC.gson.fromJson(jsonReader, MAP_STRING_VALUE));
        }
    }
}
