package tlc2.mbtc;

import tlc2.value.impl.Value;
import util.Assert;

import java.io.*;
import java.nio.file.FileVisitResult;
import java.nio.file.FileVisitor;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.Objects;

public class Misc {
    static final boolean DEBUG = true;

    static void copyFiles(String suffix, Path specDir, Path dir) throws IOException {
        Files.walkFileTree(specDir, new FileVisitor<Path>() {
            @Override
            public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) {
                return FileVisitResult.CONTINUE;
            }

            @Override
            public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
                if (file.toString().endsWith(suffix)) {
                    Files.copy(file, dir.resolve(file.getFileName()));
                }
                return FileVisitResult.CONTINUE;
            }

            @Override
            public FileVisitResult visitFileFailed(Path file, IOException exc) {
                return FileVisitResult.CONTINUE;
            }

            @Override
            public FileVisitResult postVisitDirectory(Path dir, IOException exc) {
                return FileVisitResult.CONTINUE;
            }
        });
    }

    public static <T> T readJson(String path, Class<T> c) throws IOException {
        try (Reader reader = new FileReader(path)) {
            return Objects.requireNonNull(MBTC.gson.fromJson(reader, c));
        }
    }

    public static void writeToJson(Object obj, String filename) throws IOException {
        try (Writer writer = new FileWriter(filename)) {
            MBTC.gson.toJson(obj, writer);
        }
    }

    public static void ensure(boolean cond) {
        if (!cond) {
            throw new IllegalStateException();
        }
    }

    public static void log(String s, Object... stuff) {
        if (!DEBUG) {
            return;
        }
        System.out.printf(s + "\n", stuff);
    }

    static boolean valueEqual(Value a, Value b) {
        if (!a.getClass().equals(b.getClass())) {
            return false;
        }
        try {
            return a.equals(b);
        } catch (Assert.TLCRuntimeException e) {
            return false;
        }
    }
}
