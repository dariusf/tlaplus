package tlc2.monitor;

public class GoBlock {
    String block;

    public GoBlock(String block) {
        this.block = block;
    }

    public GoBlock seq(GoBlock other) {
        return new GoBlock(block + other.block);
    }

    @Override
    public String toString() {
        return block;
    }
}
