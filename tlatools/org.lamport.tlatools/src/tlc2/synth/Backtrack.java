package tlc2.synth;

import java.util.function.Function;
import java.util.function.Supplier;

// https://okmij.org/ftp/Haskell/FBackTrack.hs
//public interface Backtrack<T> {
//    static <A> Backtrack<A> of(A elt) {
//        return new One<>(elt);
//    }
//    <A> Backtrack<A> flatMap(Function<T, Backtrack<A>> f);
//    static <A> Backtrack<A> mzero() {
//        return new Nil<>();
//    }
//    Backtrack<T> mplus(Backtrack<T> o);
//
//    default Backtrack<Void> guard(boolean b) {
//        if (b) {
//            return Backtrack.of(null);
//        } else {
//            return mzero();
//        }
//    }
//}
//final class Nil<T> implements Backtrack<T> {
//    @Override
//    public <A> Backtrack<A> flatMap(Function<T, Backtrack<A>> f) {
//        return new Nil<>();
//    }
//
//    @Override
//    public Backtrack<T> mplus(Backtrack<T> o) {
//        return new Incomplete<>(o);
//    }
//}
//final class One<T> implements Backtrack<T> {
//    T elt;
//
//    public One(T elt) {
//        this.elt = elt;
//    }
//
//    @Override
//    public <A> Backtrack<A> flatMap(Function<T, Backtrack<A>> f) {
//        return f.apply(this.elt);
//    }
//
//    @Override
//    public Backtrack<T> mplus(Backtrack<T> o) {
//        return new Choice<>(this.elt, o);
//    }
//}
//final class Choice<T> implements Backtrack<T> {
//    T elt;
//    Backtrack<T> tail;
//
//    public Choice(T elt, Backtrack<T> tail) {
//        this.elt = elt;
//        this.tail = tail;
//    }
//
//    @Override
//    public <A> Backtrack<A> flatMap(Function<T, Backtrack<A>> f) {
//        return f.apply(this.elt).mplus(new Incomplete<>(this.tail.flatMap(f)));
//    }
//
//    @Override
//    public Backtrack<T> mplus(Backtrack<T> o) {
//        return new Choice<>(this.elt, o.mplus(this.tail)); // interleaving!
//    }
//}
//final class Incomplete<T> implements Backtrack<T> {
//    Backtrack<T> tail;
//
//    public Incomplete(Backtrack<T> tail) {
//        this.tail = tail;
//    }
//
//    @Override
//    public <A> Backtrack<A> flatMap(Function<T, Backtrack<A>> f) {
//        return new Incomplete<>(this.tail.flatMap(f));
//    }
//
//    @Override
//    public Backtrack<T> mplus(Backtrack<T> o) {
//        if (o instanceof Nil<?>) {
//            return this;
//        }
//        if (o instanceof One<?>) {
//            return new Choice<>(((One<T>) o).elt, this.tail);
//        }
//        if (o instanceof Choice<?>) {
//            return new Choice<>(((Choice<T>) o).elt, this.tail.mplus(o));
//        }
//        if (o instanceof Incomplete<?>) {
//            return new Incomplete<>(this.tail.mplus(((Incomplete<T>) o).tail));
//        }
//        throw new IllegalStateException();
//    }
//
//}

// https://okmij.org/ftp/Haskell/FBackTrack.hs
public interface Backtrack<T> {
    static <A> Backtrack<A> of(A elt) {
        return new One<>(elt);
    }
    <A> Backtrack<A> flatMap(Function<T, Backtrack<A>> f);
    static <A> Backtrack<A> mzero() {
        return new Nil<>();
    }
    Backtrack<T> mplus(Supplier<Backtrack<T>> o);

    default Backtrack<Void> guard(boolean b) {
        if (b) {
            return Backtrack.of(null);
        } else {
            return mzero();
        }
    }
}
final class Nil<T> implements Backtrack<T> {
    @Override
    public <A> Backtrack<A> flatMap(Function<T, Backtrack<A>> f) {
        return new Nil<>();
    }

    @Override
    public Backtrack<T> mplus(Supplier<Backtrack<T>> o) {
        return new Incomplete<>(o);
    }
}
final class One<T> implements Backtrack<T> {
    T elt;

    public One(T elt) {
        this.elt = elt;
    }

    @Override
    public <A> Backtrack<A> flatMap(Function<T, Backtrack<A>> f) {
        return f.apply(this.elt);
    }

    @Override
    public Backtrack<T> mplus(Supplier<Backtrack<T>> o) {
        return new Choice<>(this.elt, o.get());
    }
}
final class Choice<T> implements Backtrack<T> {
    T elt;
    Backtrack<T> tail;

    public Choice(T elt, Backtrack<T> tail) {
        this.elt = elt;
        this.tail = tail;
    }

    @Override
    public <A> Backtrack<A> flatMap(Function<T, Backtrack<A>> f) {
        return f.apply(this.elt).mplus(() -> new Incomplete<>(() -> this.tail.flatMap(f)));
    }

    @Override
    public Backtrack<T> mplus(Supplier<Backtrack<T>> o) {
        return new Choice<>(this.elt, o.get().mplus(() -> this.tail)); // interleaving!
    }
}
final class Incomplete<T> implements Backtrack<T> {
    Supplier<Backtrack<T>> tail;

    public Incomplete(Supplier<Backtrack<T>> o) {
        this.tail = o;
    }

    @Override
    public <A> Backtrack<A> flatMap(Function<T, Backtrack<A>> f) {
        return new Incomplete<>(() -> this.tail.get().flatMap(f));
    }

    @Override
    public Backtrack<T> mplus(Supplier<Backtrack<T>> o) {
        if (o.get() instanceof Nil<?>) {
            return this;
        }
        if (o.get() instanceof One<?>) {
            return new Choice<>(((One<T>) o.get()).elt, this.tail.get());
        }
        if (o.get() instanceof Choice<?>) {
            return new Choice<>(((Choice<T>) o.get()).elt, this.tail.get().mplus(o));
        }
        if (o.get() instanceof Incomplete<?>) {
            return new Incomplete<>(() -> this.tail.get().mplus(() -> ((Incomplete<T>) o.get()).tail.get()));
        }
        throw new IllegalStateException();
    }

}


class Test {
    static Backtrack<Integer> nats() {
        return new Incomplete<>(() -> nats().flatMap(n -> Backtrack.of(n + 1)))
                .mplus(() -> Backtrack.of(0));
    }
    public static void main(String[] args) {
        Backtrack<Integer> n = nats();
    }
}
