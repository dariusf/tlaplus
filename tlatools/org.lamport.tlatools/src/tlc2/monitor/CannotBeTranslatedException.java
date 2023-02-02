package tlc2.monitor;

public class CannotBeTranslatedException extends RuntimeException {
    public CannotBeTranslatedException(String message) {
        super(message);
    }
}
