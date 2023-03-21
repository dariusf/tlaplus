package tlc2.mbtc;

import com.google.gson.JsonDeserializationContext;
import com.google.gson.JsonDeserializer;
import com.google.gson.JsonElement;
import com.google.gson.JsonParseException;
import tlc2.module.Json;
import tlc2.value.impl.Value;

import java.io.IOException;
import java.lang.reflect.Type;

public class ValueDeserializer implements JsonDeserializer<Value> {
    @Override
    public Value deserialize(JsonElement jsonElement, Type type, JsonDeserializationContext jsonDeserializationContext) throws JsonParseException {
        try {
            return Json.getValue(jsonElement);
        } catch (IOException e) {
            throw new JsonParseException(e);
        }
    }
}
