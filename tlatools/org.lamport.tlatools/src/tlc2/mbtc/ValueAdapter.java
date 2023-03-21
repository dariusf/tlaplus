package tlc2.mbtc;

import com.google.gson.*;
import tlc2.module.Json;
import tlc2.value.impl.Value;

import java.io.IOException;
import java.lang.reflect.Type;

public class ValueAdapter implements JsonSerializer<Value>, JsonDeserializer<Value> {
    @Override
    public Value deserialize(JsonElement jsonElement, Type type, JsonDeserializationContext jsonDeserializationContext) throws JsonParseException {
        try {
            return Json.getValue(jsonElement);
        } catch (IOException e) {
            throw new JsonParseException(e);
        }
    }

    @Override
    public JsonElement serialize(Value value, Type type, JsonSerializationContext jsonSerializationContext) {
        try {
            return Json.getNode(value);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
