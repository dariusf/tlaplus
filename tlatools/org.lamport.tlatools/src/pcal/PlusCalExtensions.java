package pcal;

import pcal.exception.ParseAlgorithmException;
import pcal.exception.TokenizerException;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static pcal.ParseAlgorithm.*;

public class PlusCalExtensions {

    private static class Party {
        final String partyVar;
        final boolean equalOrIn;
        final TLAExpr partySet;

        final List<AST.VarDecl> localVars;

        private Party(String partyVar, boolean equalOrIn, TLAExpr partySet, List<AST.VarDecl> localVars) {
            this.partyVar = partyVar;
            this.equalOrIn = equalOrIn;
            this.partySet = partySet;
            this.localVars = localVars;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Party party = (Party) o;
            return equalOrIn == party.equalOrIn && Objects.equals(partyVar, party.partyVar) && Objects.equals(partySet, party.partySet) && Objects.equals(localVars, party.localVars);
        }

        @Override
        public int hashCode() {
            return Objects.hash(partyVar, equalOrIn, partySet, localVars);
        }
    }

    static class Context {

        // task id -> Party
        Map<String, Party> taskOwnership;

        // TODO remove
        Map<String, AST.Cancel> cancellations;

        Vector<AST.VarDecl> globals;

        // party task id variable -> party
        Map<String, Party> partyDecls;

        // variable -> party
        Map<String, Party> ownership;

        // For things like while, which use positional expressions for parties
        List<Party> partiesOrdered;
    }

    public static AST GetAll(int depth) throws ParseAlgorithmException {
        return InnerGetAll(depth, null);
    }

    /**
     * Just a with statement with different keyword, return type, constructor, error messages.
     * The reason we don't parameterize {@link ParseAlgorithm#InnerGetWith} is that there is no supertype of With/All
     * that has all the fields we need to assign.
     */
    public static AST.All InnerGetAll(int depth, PCalLocation beginLoc) throws ParseAlgorithmException {
        PCalLocation begLoc = beginLoc;
        if (depth == 0) {
            GobbleThis("all");
            begLoc = GetLastLocationStart();
            if (cSyntax) {
                GobbleThis("(");
            }
            ;
        }
        ;
        AST.All result = new AST.All();
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.var = GetAlgToken();
        result.isEq = GobbleEqualOrIf();
        result.exp = GetExpr();
        if (pSyntax || !PeekAtAlgToken(1).equals(")")) {
            GobbleCommaOrSemicolon();
            /**************************************************************
             * Gobble the ";" or "," ending the <VarEqOrIn>, which may be  *
             * eliminated before a ")" or "do".                            *
             **************************************************************/
        }
        ;
        if (result.exp.tokens.size() == 0) {
            ParsingError("Empty all expression at ");
        }
        ;
        if (pSyntax && PeekAtAlgToken(1).equals("do")) {
            GobbleThis("do");
            result.Do = GetStmtSeq();
            GobbleThis("end");
            GobbleThis("all");
            GobbleThis(";");
        } else if (cSyntax && PeekAtAlgToken(1).equals(")")) {
            MustGobbleThis(")");
            result.Do = GetCStmt();
        } else {
            result.Do = new Vector();
            result.Do.addElement(InnerGetAll(depth + 1, begLoc));
        }
        ;
        try {
            result.setOrigin(new Region(begLoc,
                    ((AST) result.Do.elementAt(result.Do.size() - 1)).getOrigin().getEnd()));
        } catch (ArrayIndexOutOfBoundsException e) {
            throw new ParseAlgorithmException("Missing body of all statement", result);
        }
        return result;
    }

    public static AST.Task GetTask() throws ParseAlgorithmException {
//        if (depth == 0)
//        {
        GobbleThis("task");
        PCalLocation begLoc = GetLastLocationStart();
//            if (cSyntax) { GobbleThis("(") ; } ;
//        } ;

        AST.Task result = new AST.Task();
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.partyId = GetExpr();
        GobbleCommaOrSemicolon();
        result.taskId = GetAlgToken();
//        result.isEq = GobbleEqualOrIf() ;
//        result.exp  = GetExpr() ;
//        if (pSyntax || ! PeekAtAlgToken(1).equals(")"))
//        { GobbleCommaOrSemicolon();
//            /**************************************************************
//             * Gobble the ";" or "," ending the <VarEqOrIn>, which may be  *
//             * eliminated before a ")" or "do".                            *
//             **************************************************************/
//        } ;
//        if (result.exp.tokens.size() == 0)
//        { ParsingError("Empty all expression at ") ;} ;
        if (pSyntax && PeekAtAlgToken(1).equals("do")) {
            GobbleThis("do");
            result.Do = GetStmtSeq();
            GobbleThis("end");
//            GobbleThis("all") ;
            GobbleThis("task");
            GobbleThis(";");
        } else if (cSyntax) // && PeekAtAlgToken(1).equals(")"))
        { //MustGobbleThis(")") ;
            result.Do = GetCStmt();
        }
//        else
//        { result.Do = new Vector() ;
//            result.Do.addElement(InnerGetAll(depth+1, begLoc)) ;
//        };
        try {
            result.setOrigin(new Region(begLoc,
                    ((AST) result.Do.elementAt(result.Do.size() - 1)).getOrigin().getEnd()));
        } catch (ArrayIndexOutOfBoundsException e) {
            throw new ParseAlgorithmException("Missing body of task statement", result);
        }
        return result;
    }

    public static List<AST.Process> GetChoreography(Vector<AST.VarDecl> globals,
                                                    Vector<AST.Macro> macros) throws ParseAlgorithmException {
        GobbleThis("choreography");

        Context ctx = new Context();
        ctx.globals = globals;
        ctx.partyDecls = new HashMap<>();
        ctx.ownership = new HashMap<>();
        ctx.partiesOrdered = new ArrayList<>();

        // Parse party declarations
        while (PeekAtAlgToken(1).equals("(")) {
            GobbleThis("(");
            String partyVar = GetAlgToken();
            boolean eqOrIn = GobbleEqualOrIf();
            TLAExpr partySet = GetExpr();
            GobbleThis(")");
            List<AST.VarDecl> localVars = new ArrayList<>();
            if (PeekAtAlgToken(1).equals("variables")) {
                localVars = new ArrayList<>(GetVarDecls());
            } else {
                // no variables declared, so consume the delimiter which would otherwise
                // be consumed by var decls
                GobbleCommaOrSemicolon();
            }
            Party party = new Party(partyVar, eqOrIn, partySet, localVars);
            ctx.partyDecls.put(partyVar, party);
            ctx.partiesOrdered.add(party);
            if (eqOrIn) { // is equal
                // add constant exprs to ownership
                ctx.ownership.put(tlaExprAsVar(partySet), party);
            }
        }

        GobbleBeginOrLeftBrace();
        Vector<AST> stmts = GetStmtSeq();
        GobbleEndOrRightBrace("choreography");

        //////
        // Translate into regular PlusCal
        //////

        // Preprocessing to handle cancellations
        ctx.cancellations = new HashMap<>();
        ctx.taskOwnership = new HashMap<>();
        findTasks(ctx, ctx.taskOwnership, stmts);

        // Add global variables corresponding to cancellations
        findCancellations(ctx.cancellations, stmts);
        ctx.cancellations.forEach((key, value) -> {
            AST.VarDecl v = new AST.VarDecl();
            v.var = String.format("cancelled_%s", key);
            v.val = tlaExpr("FALSE");
            v.isEq = true;
            globals.add(v);
        });

        // don't transform away cancellations until after projection

        // Ownership and projection
        Map<String, Party> quantified = computeOwnership(ctx.partyDecls, stmts);
        ctx.ownership.putAll(quantified);
        Map<Party, AST.Process> res = project(ctx, stmts);

        res.entrySet().stream()
                .sorted(Comparator.comparing(e -> e.getKey().partyVar)) // det
                .forEach(e -> System.out.printf("Projection of %s:\n\n%s\n\n",
                        Printer.show(e.getKey().partySet),
                        Printer.show(e.getValue())));

        // Post-projection elaboration
        List<AST.Process> res1 = res.entrySet().stream()
                .flatMap(p -> expandParStatement(p.getKey(), p.getValue()).stream().map(pr -> new AbstractMap.SimpleEntry<>(p.getKey(), pr)))
                .flatMap(p -> expandAllStatement(p.getKey(), p.getValue()).stream().map(pr -> new AbstractMap.SimpleEntry<>(p.getKey(), pr)))
                .flatMap(p -> expandCancellations(p.getValue()).stream().map(pr -> new AbstractMap.SimpleEntry<>(p.getKey(), pr)))
                .map(Map.Entry::getValue)
                .map(PlusCalExtensions::expandTask)
                .collect(Collectors.toList());

        // TODO optimize, remove the no-op processes entirely

        System.out.println("Final processes:\n");
        res1.stream().map(Printer::show)
                .sorted() // det
                .forEach(System.out::println);

        return res1;
    }

    private static void findTasks(Context ctx, Map<String, Party> tasks, Vector<AST> stmts) {
        stmts.forEach(s -> findTasks(ctx, tasks, s));
    }

    private static void findTasks(Context ctx, Map<String, Party> res, AST stmt) {
        if (stmt instanceof AST.All) {
            findTasks(ctx, res, ((AST.All) stmt).Do);
        } else if (stmt instanceof AST.LabelEither) {
            findTasks(ctx, res, ((AST.LabelEither) stmt).clauses);
        } else if (stmt instanceof AST.Par) {
            findTasks(ctx, res, ((AST.Par) stmt).clauses);
        } else if (stmt instanceof AST.LabelIf) {
            findTasks(ctx, res, ((AST.LabelIf) stmt).unlabElse);
            findTasks(ctx, res, ((AST.LabelIf) stmt).unlabThen);
            findTasks(ctx, res, ((AST.LabelIf) stmt).labElse);
            findTasks(ctx, res, ((AST.LabelIf) stmt).labThen);
        } else if (stmt instanceof AST.With) {
            findTasks(ctx, res, ((AST.With) stmt).Do);
        } else if (stmt instanceof AST.Task) {
            AST.Task task = (AST.Task) stmt;
            res.put(task.taskId, ctx.partyDecls.get(Printer.show(task.partyId)));
            findTasks(ctx, res, task.Do);
        } else if (stmt instanceof AST.While) {
            AST.While w = (AST.While) stmt;
            findTasks(ctx, res, w.unlabDo);
            findTasks(ctx, res, w.labDo);
        } else if (stmt instanceof AST.When) {
            // nothing to do
        } else if (stmt instanceof AST.Clause) {
            findTasks(ctx, res, ((AST.Clause) stmt).labOr);
            findTasks(ctx, res, ((AST.Clause) stmt).unlabOr);
        } else if (stmt instanceof AST.Assign) {
            // nothing
        } else if (stmt instanceof AST.SingleAssign) {
            // nothing
        } else if (stmt instanceof AST.Cancel) {
            // nothing
        } else if (stmt instanceof AST.MacroCall) {
            // nothing
        } else {
            fail("unimplemented findTasks " + stmt);
        }
    }

    private static void findCancellations(Map<String, AST.Cancel> res, Vector<AST> stmts) {
        stmts.forEach(s -> findCancellations(res, s));
    }

    // Build a map of task id -> cancellations for that id
    private static void findCancellations(Map<String, AST.Cancel> res, AST stmt) {
        if (stmt instanceof AST.All) {
            findCancellations(res, ((AST.All) stmt).Do);
        } else if (stmt instanceof AST.LabelEither) {
            findCancellations(res, ((AST.LabelEither) stmt).clauses);
        } else if (stmt instanceof AST.Par) {
            findCancellations(res, ((AST.Par) stmt).clauses);
        } else if (stmt instanceof AST.LabelIf) {
            findCancellations(res, ((AST.LabelIf) stmt).unlabElse);
            findCancellations(res, ((AST.LabelIf) stmt).unlabThen);
            findCancellations(res, ((AST.LabelIf) stmt).labElse);
            findCancellations(res, ((AST.LabelIf) stmt).labThen);
        } else if (stmt instanceof AST.With) {
            findCancellations(res, ((AST.With) stmt).Do);
        } else if (stmt instanceof AST.Task) {
            findCancellations(res, ((AST.Task) stmt).Do);
        } else if (stmt instanceof AST.When) {
            // nothing to do
        } else if (stmt instanceof AST.Clause) {
            findCancellations(res, ((AST.Clause) stmt).labOr);
            findCancellations(res, ((AST.Clause) stmt).unlabOr);
        } else if (stmt instanceof AST.While) {
            findCancellations(res, ((AST.While) stmt).labDo);
            findCancellations(res, ((AST.While) stmt).unlabDo);
        } else if (stmt instanceof AST.Assign) {
            // nothing
        } else if (stmt instanceof AST.SingleAssign) {
            // nothing
        } else if (stmt instanceof AST.Cancel) {
            res.put(((AST.Cancel) stmt).task, (AST.Cancel) stmt);
        } else if (stmt instanceof AST.MacroCall) {
            // nothing
        } else {
            fail("unimplemented findCancellations " + stmt);
        }
    }

    /**
     * So when transforming a process recursively, anything nested inside can expand into more processes
     */
    static class WithProc<T> {
        final T thing;
        final List<AST.Process> procs;

        public WithProc(T thing, List<AST.Process> procs) {
            this.thing = thing;
            this.procs = procs;
        }

        /**
         * Merges these two WithProcs, but throws away the result of the other
         * (hence the name; this subsumes)
         */
//        WithProc<T> subsume(WithProc<T> other) {
//            List<AST.Process> ps = new ArrayList<>();
//            ps.addAll(procs);
//            ps.addAll(other.procs);
//            return new WithProc<>(thing, ps);
//        }

        <B> WithProc<B> map(Function<T, B> f) {
            return new WithProc<>(f.apply(this.thing), procs);
        }

        WithProc<T> addAll(Collection<AST.Process> proc) {
            List<AST.Process> ps = new ArrayList<>(procs);
            ps.addAll(proc);
            return new WithProc<>(thing, ps);
        }

        WithProc<T> add(AST.Process proc) {
            List<AST.Process> ps = new ArrayList<>(procs);
            ps.add(proc);
            return new WithProc<>(thing, ps);
        }

        static <T> WithProc<List<T>> sequence(List<WithProc<T>> inp) {
            List<T> res = new ArrayList<>();
            List<AST.Process> procs = new ArrayList<>();
            inp.forEach(i -> {
                procs.addAll(i.procs);
                res.add(i.thing);
            });
            return new WithProc<>(res, procs);
        }

        static <T> WithProc<Vector<T>> sequenceV(List<WithProc<T>> inp) {
            return sequence(inp).map(Vector::new);
        }
    }

    /**
     * This is essentially {@link ParseAlgorithm#GetEither()} with the keywords changed
     */
    public static AST.Par GetPar() throws ParseAlgorithmException {
        MustGobbleThis("par");
        PCalLocation beginLoc = GetLastLocationStart();
        AST.Par result = new AST.Par();
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.clauses = new Vector();
        boolean done = false;
        boolean hasOr = false;
        while (!done) {
            AST.Clause nextClause = new AST.Clause();
            nextClause.labOr = new Vector();
            if (pSyntax) {
                nextClause.unlabOr = GetStmtSeq();
            } else {
                nextClause.unlabOr = GetCStmt();
            }
            if (nextClause.unlabOr.size() == 0) {
                throw new ParseAlgorithmException(
                        "`par' statement with empty `and' clause", result);
            }
            ;
            nextClause.setOrigin(new Region(
                    ((AST) nextClause.unlabOr.elementAt(0)).getOrigin().getBegin(),
                    ((AST) nextClause.unlabOr.elementAt(nextClause.unlabOr.size() - 1))
                            .getOrigin().getEnd()));
            result.clauses.addElement(nextClause);
            String nextTok = PeekAtAlgToken(1);
            if (nextTok.equals("and")) {
                MustGobbleThis("and");
                hasOr = true;
            } else {
                done = true;
            }
        }
        ;
        if (pSyntax) {
            MustGobbleThis("end");
            GobbleThis("par");
            GobbleThis(";");
        }
        ;
        if (!hasOr) {
            throw new ParseAlgorithmException("`par' statement has no `and'", result);
        }
        ;
        result.setOrigin(new Region(beginLoc,
                ((AST) result.clauses.elementAt(result.clauses.size() - 1))
                        .getOrigin().getEnd()));
        return result;
    }

    /**
     * Very similar to {@link ParseAlgorithm#GetGoto()}
     */
    public static AST.Cancel GetCancel() throws ParseAlgorithmException {
        MustGobbleThis("cancel");
        AST.Cancel result = new AST.Cancel();
        result.col = lastTokCol;
        result.line = lastTokLine;
        result.task = GetAlgToken();
        result.setOrigin(new Region(new PCalLocation(result.line - 1, result.col - 1),
                new PCalLocation(lastTokLine - 1, lastTokCol - 1 + result.task.length())));
        GobbleThis(";");
        return result;
    }

    private static List<AST.Process> expandCancellations(AST.Process proc) {
        return transformProcessBody(proc, s -> new WithProc<>(transformCancellations(s), List.of()));
    }


    private static AST.Process flatMapProcessBody(AST.Process proc,
                                                  Function<AST, Stream<AST>> f) {
        List<AST> res = ((Vector<AST>) proc.body).stream()
                .flatMap(f)
                .collect(Collectors.toList());

//        List<AST> body1 = res.stream()
//                .map(wp -> wp.thing)
//                .collect(Collectors.toList());

        AST.Process proc1 = createProcess(proc.name, proc.isEq, proc.id, new Vector<>(res), proc.decls);

//        List<AST.Process> newProcesses = res.stream()
//                .flatMap(wp -> wp.procs.stream())
//                .collect(Collectors.toCollection(ArrayList::new));
//        newProcesses.add(proc1);
//        return newProcesses;

        return proc1;
    }

    private static AST.Process expandTask(AST.Process proc) {
        return flatMapProcessBody(proc, s -> transformTask(s, Optional.empty()));
    }

    private static void copyInto(AST to, AST from) {
        to.lbl = from.lbl;
        to.lblLocation = from.lblLocation;
        to.setOrigin(from.getOrigin());
    }

    private static AST.Par newPar(AST.Par e) {
        AST.Par e1 = new AST.Par();
        copyInto(e1, e);
        return e1;
    }

    private static AST.LabelEither newEither(AST.LabelEither e) {
        AST.LabelEither e1 = new AST.LabelEither();
        e1.clauses = e.clauses;
        copyInto(e1, e);
        return e1;
    }

    // stmt is the statement we are transforming, task is the closest enclosing task
    // returns a stream because this may remove a task, resulting in a bunch of statements
    private static Stream<AST> transformTask(AST stmt, Optional<AST.Task> task) {
        Stream<AST> res;
        boolean statefulMaybe = false;
        if (stmt instanceof AST.All) {
            AST.All e = (AST.All) stmt;
            AST.All e1 = newAll(e);
            e1.Do = ((Stream<AST>) transformTask(e.Do, task)).collect(Collectors.toCollection(Vector::new));
            res = Stream.of(e1);
        } else if (stmt instanceof AST.While) {
            AST.While e = (AST.While) stmt;
            AST.While e1 = newWhile(e);
            e1.unlabDo = ((Stream<AST>) transformTask(e.unlabDo, task)).collect(Collectors.toCollection(Vector::new));
            e1.labDo = ((Stream<AST>) transformTask(e.labDo, task)).collect(Collectors.toCollection(Vector::new));
            res = Stream.of(e1);
        } else if (stmt instanceof AST.LabelEither) {
            AST.LabelEither e = (AST.LabelEither) stmt;
            AST.LabelEither e1 = newEither(e);
            e1.clauses = ((Stream<AST>) transformTask(e.clauses, task)).collect(Collectors.toCollection(Vector::new));
            res = Stream.of(e1);
        } else if (stmt instanceof AST.Par) {
            AST.Par e = (AST.Par) stmt;
            AST.Par e1 = newPar(e);
            e1.clauses = ((Stream<AST>) transformTask(e.clauses, task)).collect(Collectors.toCollection(Vector::new));
            res = Stream.of(e1);
        } else if (stmt instanceof AST.Task) {
            AST.Task e = (AST.Task) stmt;
//            if (e.lbl != null) {
//                fail("tasks cannot have labels, as it is unclear how many statements in their body the label should apply to");
//            }
            res = ((Stream<AST>) transformTask(e.Do, Optional.of(e)));
//        } else if (stmt instanceof AST.With) {
            // TODO
//            res = Stream.of(e1);
        } else if (stmt instanceof AST.LabelIf) {
            AST.LabelIf e = (AST.LabelIf) stmt;
            AST.LabelIf e1 = newIf(e);
            e1.labElse = ((Stream<AST>) transformTask(e.labElse, task)).collect(Collectors.toCollection(Vector::new));
            e1.labThen = ((Stream<AST>) transformTask(e.labThen, task)).collect(Collectors.toCollection(Vector::new));
            e1.unlabElse = ((Stream<AST>) transformTask(e.unlabElse, task)).collect(Collectors.toCollection(Vector::new));
            e1.unlabThen = ((Stream<AST>) transformTask(e.unlabThen, task)).collect(Collectors.toCollection(Vector::new));
            res = Stream.of(e1);
        } else if (stmt instanceof AST.Clause) {
            AST.Clause e = (AST.Clause) stmt;
            AST.Clause e1 = new AST.Clause();
            e1.labOr = e.labOr;
            e1.unlabOr = e1.labOr;
            copyInto(e1, e);
            e1.labOr = ((Stream<AST>) transformTask(e.labOr, task)).collect(Collectors.toCollection(Vector::new));
            e1.unlabOr = ((Stream<AST>) transformTask(e.unlabOr, task)).collect(Collectors.toCollection(Vector::new));
            res = Stream.of(e1);
        } else if (stmt instanceof AST.When) {
            statefulMaybe = true;
            res = Stream.of(stmt);
        } else if (stmt instanceof AST.Assign) {
            statefulMaybe = true;
            res = Stream.of(stmt);
        } else if (stmt instanceof AST.SingleAssign) {
            statefulMaybe = true;
            res = Stream.of(stmt);
        } else if (stmt instanceof AST.Cancel) {
            statefulMaybe = true;
            res = Stream.of(stmt);
        } else if (stmt instanceof AST.MacroCall) {
            statefulMaybe = true;
            res = Stream.of(stmt);
        } else if (stmt instanceof AST.Skip) {
            res = Stream.of(stmt);
        } else {
            fail("transformTask: unimplemented " + stmt);
            return null;
        }
        if (task.isEmpty() || !statefulMaybe) {
            // if not inside a task
            return res;
        } else {
            String v = String.format("cancelled_%s", task.get().taskId);
            AST.LabelIf check = makeConditional(res, tlaExpr("~ %s", v));
            return Stream.of(check);
        }
    }

    public static void require(boolean precondition) {
        if (!precondition) {
            throw new IllegalArgumentException();
        }
    }

    private static AST.LabelIf makeConditional(Stream<AST> res, TLAExpr test) {
        List<AST> thenContents = res.collect(Collectors.toList());
        require(!thenContents.isEmpty());

        AST.LabelIf check = new AST.LabelIf();
        check.setOrigin(thenContents.get(0).getOrigin());
        check.test = test;

        Vector<AST> then1 = new Vector<>();
        then1.addAll(thenContents);
        check.unlabThen = then1;

        AST noop = new AST.Skip();
        Vector<AST> else1 = new Vector<>();
        else1.add(noop);
        check.unlabElse = else1;
        return check;
    }

    private static Stream<AST> transformTask(Vector<AST> s, Optional<AST.Task> task) {
//        return s.stream().flatMap(s1 -> transformTaskAwait(s1, task));
        return s.stream().flatMap(s1 -> transformTask(s1, task));
    }

    /**
     * Expand occurrences of par statements in a process
     */
    private static List<AST.Process> expandParStatement(Party which, AST.Process proc) {
        return transformProcessBody(proc, s -> expandParStatement(which, s));
    }

    /**
     * f is a function for transforming single statements and possibly generating more processes
     */
    private static List<AST.Process> transformProcessBody(AST.Process proc,
                                                          Function<AST, WithProc<AST>> f) {
        List<WithProc<AST>> res = ((Vector<AST>) proc.body).stream()
                .map(f)
                .collect(Collectors.toList());

        List<AST> body1 = res.stream()
                .map(wp -> wp.thing)
                .collect(Collectors.toList());

        AST.Process proc1 = createProcess(proc.name, proc.isEq, proc.id, new Vector<>(body1), proc.decls);

        List<AST.Process> newProcesses = res.stream()
                .flatMap(wp -> wp.procs.stream())
                .collect(Collectors.toCollection(ArrayList::new));

        newProcesses.add(proc1);

        return newProcesses;
    }

    private static List<AST.Process> expandAllStatement(Party party, AST.Process proc) {
        return transformProcessBody(proc, s -> expandAllStatement(party, s));
    }

    private static AST.Process createProcess(String name, boolean isEq, TLAExpr id,
                                             Vector<AST> body, Vector<AST.VarDecl> decls) {
        // TODO see what else GetProcess does
        AST.Process proc1 = new AST.Process();
        proc1.name = name;
        proc1.isEq = isEq;
        proc1.id = id;
        proc1.body = body;
        proc1.decls = decls;
        proc1.plusLabels = new Vector<>(0);
        proc1.minusLabels = new Vector<>(0);
        proc1.proceduresCalled = new Vector<>(0);
        proc1.setOrigin(new Region(0, 0, 0));
        return proc1;
    }

    private static TLAExpr tlaExpr(String fmt, Object... args) {
        for (int i = 0; i < args.length; i++) {
            if (args[i] instanceof TLAExpr) {
                args[i] = Printer.show((TLAExpr) args[i]);
            }
        }
        String s = String.format(fmt, args);
        Vector<String> line = new Vector<>();
        line.add(s);
        PcalCharReader reader = new PcalCharReader(line, 0, 0, 1, 0);
        try {
            TLAExpr e = Tokenize.TokenizeExpr(reader);
            e.setOrigin(new Region(0, 0, 0));
            return e;
        } catch (TokenizerException e) {
            throw new RuntimeException(e);
        }
    }

    private static int varI;

    static String fresh(String prefix) {
        return prefix + "_" + (varI++);
    }

    /**
     * Turn a single par clause into its own process
     */
    private static AST.Process parStatementProcess(String label, TLAExpr set, AST.Clause cl) {
        String processActionName = fresh("proc");
        Vector<AST.VarDecl> decls = new Vector<>();
        Vector<AST> body = new Vector<>();
        AST.When wait = new AST.When();
        wait.exp = tlaExpr("pc[Head(self)] = \"%s\"", label);
        wait.setOrigin(set.getOrigin());
        body.add(wait);
        if (cl.unlabOr != null) {
            body.addAll(cl.unlabOr);
        } else {
            body.addAll(cl.labOr);
        }
        return createProcess(processActionName, false, set, body, decls);
    }

    /*
     parameters: q, qs

     process (m = main)
        ...
     {
         all (q \in qs) {
            ...
         }
     }

     translates to two processes:

     process (m = main)
        ...
     {
        await ...
     }

     process (q \in qs)
        variables auxps = ps;
     {
        while (auxps /= {}) {
            with (pp \in { pr \in ps : pc[pr] = "pa" }) {
                out := out \ union {<<pp, self>>};
                auxps := auxps \ {pp};
            }
        }
     }
     */
    private static AST.Process allStatementProcess(Party party, String label,
                                                   String q, TLAExpr qs, Vector<AST> body) {
        AST.When await = new AST.When();
        await.exp = tlaExpr("pc[Head(self)] = \"%s\"", label);
        await.setOrigin(qs.getOrigin());

        Vector<AST> body1 = new Vector<>();
        body1.add(await);
        body1.addAll(body);

        TLAExpr product = tlaExpr("(%s \\X %s)", party.partySet, qs);
        return createProcess(fresh("proc"), false, product, body1, new Vector<>());
    }

    /**
     * Called for each statement of a process, which may generate more processes
     */
    private static WithProc<AST> expandParStatement(Party which, AST stmt) {
        if (stmt instanceof AST.Par) {
            // This could be translated into an All over a constant set with an if in each branch,
            // but then the output would be significantly uglier, so we do it in a simple way
            AST.Par par = (AST.Par) stmt;

            String label = fresh("par");

            AST.When wait = new AST.When();
            wait.setOrigin(stmt.getOrigin());

            List<AST.Process> newProcesses = new ArrayList<>();

            Vector<AST.Clause> clauses = par.clauses;
            List<AbstractMap.SimpleEntry<String, AST.Process>> threads = clauses.stream().map(c -> {
                String p = fresh(which.partyVar + "_par");
                String id = String.format("\"%s\"", p);
                TLAExpr set = tlaExpr("(%s \\X {%s})", which.partySet, id);

                // recurse and non-algebraically accumulate the new processes
                AST.Clause c1 = new AST.Clause();
                if (c.unlabOr != null) {
                    WithProc<Vector<AST>> wp = expandParStatement(which, (Vector<AST>) c.unlabOr);
                    newProcesses.addAll(wp.procs);
                    c1.unlabOr = new Vector<>(wp.thing);
                } else {
                    WithProc<Vector<AST>> wp = expandParStatement(which, (Vector<AST>) c.labOr);
                    newProcesses.addAll(wp.procs);
                    c1.labOr = new Vector<>(wp.thing);
                }
                copyInto(c1, c);

                return new AbstractMap.SimpleEntry<>(id, parStatementProcess(label, set, c1));
            }).collect(Collectors.toList());

            String var = fresh("v");
            String tids = threads.stream()
                    .map(AbstractMap.SimpleEntry::getKey)
                    .collect(Collectors.joining(", "));
            List<AST.Process> processesFromHere = threads.stream()
                    .map(AbstractMap.SimpleEntry::getValue)
                    .collect(Collectors.toList());
            wait.exp = tlaExpr("\\A %s \\in (%s \\X {%s}) : pc[%s] = \"Done\"", var, which.partySet, tids, var);
            wait.lbl = label;

            newProcesses.addAll(processesFromHere);
            return new WithProc<>(wait, newProcesses);
        } else if (stmt instanceof AST.Task) {
            AST.Task task = (AST.Task) stmt;
            return expandParStatement(which, (Vector<AST>) task.Do).map(d -> {
                AST.Task t1 = newTask(task);
                t1.Do = d;
                return t1;
            });
        } else if (stmt instanceof AST.All) {
            AST.All task = (AST.All) stmt;
            return expandParStatement(which, (Vector<AST>) task.Do).map(d -> {
                AST.All t1 = newAll(task);
                t1.Do = d;
                return t1;
            });
        } else if (stmt instanceof AST.While) {
            AST.While task = (AST.While) stmt;
            if (task.unlabDo != null) {
                return expandParStatement(which, (Vector<AST>) task.unlabDo).map(d -> {
                    AST.While t1 = newWhile(task);
                    t1.unlabDo = d;
                    return t1;
                });
            } else {
                return expandParStatement(which, (Vector<AST>) task.labDo).map(d -> {
                    AST.While t1 = newWhile(task);
                    t1.labDo = d;
                    return t1;
                });
            }
        } else if (stmt instanceof AST.LabelEither) {
            AST.LabelEither task = (AST.LabelEither) stmt;
            return expandParStatement(which, (Vector<AST>) task.clauses).map(c -> {
                AST.LabelEither t1 = newEither(task);
                t1.clauses = c;
                return t1;
            });
        } else if (stmt instanceof AST.Cancel ||
                stmt instanceof AST.Assign ||
                stmt instanceof AST.SingleAssign ||
                stmt instanceof AST.When ||
                stmt instanceof AST.MacroCall ||
                stmt instanceof AST.Skip
        ) {
            return new WithProc<>(stmt, List.of());
        } else {
            throw new IllegalArgumentException("expandParStatement: unhandled " + stmt.getClass().getSimpleName());
        }
    }

    private static WithProc<Vector<AST>> expandParStatement(Party which, Vector<AST> stmt) {
        return WithProc.sequenceV(
                stmt.stream().map(s -> expandParStatement(which, s))
                        .collect(Collectors.toList()));
    }

    // Given an all statement, returns the await statement it is replaced with,
    // together with the process created to support it
    private static WithProc<AST> expandAllStatement(Party party, AST stmt) {
        if (stmt instanceof AST.All) {
            AST.All all = (AST.All) stmt;
            AST.When wait = new AST.When();
            wait.setOrigin(stmt.getOrigin());
            wait.exp = tlaExpr("\\A %s %s (%s \\X %s) : pc[%s] = \"Done\"",
                    all.var, all.isEq ? "=" : "\\in",
                    party.partySet, all.exp,
                    all.var);
            wait.lbl = fresh("fork");

            List<AST.Process> procs = new ArrayList<>();
            return expandAllStatement(party, (Vector<AST>) all.Do).map(d -> {
                AST.Process proc = allStatementProcess(party, wait.lbl, all.var, all.exp, d);
                procs.add(proc);
                return (AST) wait;
            }).addAll(procs);
        } else if (stmt instanceof AST.Task) {
            AST.Task t = (AST.Task) stmt;
            return expandAllStatement(party, (Vector<AST>) t.Do).map(d -> {
                AST.Task t1 = newTask(t);
                t1.Do = d;
                return t1;
            });
        } else if (stmt instanceof AST.While) {
            AST.While t = (AST.While) stmt;
            if (t.unlabDo != null) {
                return expandAllStatement(party, (Vector<AST>) t.unlabDo).map(d -> {
                    AST.While t1 = newWhile(t);
                    t1.unlabDo = d;
                    return t1;
                });
            } else {
                return expandAllStatement(party, (Vector<AST>) t.labDo).map(d -> {
                    AST.While t1 = newWhile(t);
                    t1.labDo = d;
                    return t1;
                });
            }
        } else if (stmt instanceof AST.When ||
                stmt instanceof AST.Cancel ||
                stmt instanceof AST.Skip ||
                stmt instanceof AST.MacroCall ||
                stmt instanceof AST.Assign) {
            return new WithProc<>(stmt, List.of());
        } else {
            throw new IllegalArgumentException("expandAllStatement: unhandled " + stmt.getClass().getSimpleName());
        }
    }

    private static WithProc<Vector<AST>> expandAllStatement(Party which, Vector<AST> stmt) {
        return WithProc.sequenceV(
                stmt.stream().map(s -> expandAllStatement(which, s))
                        .collect(Collectors.toList()));
    }

    static Map<String, Party> computeOwnership(Map<String, Party> partyDecls, Vector<AST> ast) {
        Map<String, Party> result = new HashMap<>();
        ast.forEach(a -> {
            Map<String, Party> r = computeOwnership(partyDecls, a);
            result.putAll(r);
        });
        return result;
    }

    static Map<String, Party> computeOwnership(Map<String, Party> partyDecls, AST ast) {
        if (ast instanceof AST.All) {
            String var = ((AST.All) ast).var;
            TLAExpr exp = ((AST.All) ast).exp;
            Optional<Party> first = partyDecls.values().stream()
                    .filter(p -> p.partySet.toString().equals(exp.toString()))
                    .findFirst();
            if (first.isPresent()) {
                Map<String, Party> res = new HashMap<>();
                res.put(var, first.get());
                res.putAll(computeOwnership(partyDecls, ((AST.All) ast).Do));
                return res;
            } else {
                fail("non constant set quantified over " + exp);
            }
            return null;
//        } else if (ast instanceof AST.MacroCall && ((AST.MacroCall) ast).name.equals("Send")) {
//            return null;
        } else {
//            fail("computeOwnership: " + ast);
            return Map.of();
        }
    }

    private static void fail(String s) {
        // so this isn't caught and surfaces to the top level
        throw new Error(s);
    }

    private static Map<Party, AST.Process> project(Context ctx, Vector<AST> stmts) {
        return ctx.partyDecls.entrySet().stream().map(e -> {
            Party party = e.getValue();
            Vector<AST> stmts1 = stmts.stream()
                    .flatMap(s -> project(ctx, party, s).stream())
                    .collect(Collectors.toCollection(Vector::new));
            AST.Process process = createProcess(party.partyVar, party.equalOrIn, party.partySet,
                    stmts1, new Vector<>(party.localVars));
            return new AbstractMap.SimpleEntry<>(party, process);
        }).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
    }

    // the role predicate from the paper, true iff e interpreted as a role is r
    public static boolean exprRole(TLAExpr e, Party r) {
        return equalModuloPrinting(e, r.partySet);
    }

    public static boolean equalModuloPrinting(TLAExpr a, TLAExpr b) {
        return Printer.show(a).equals(Printer.show(b));
    }

    /**
     * Main projection function, splitting a statement into its local equivalent for the given party,
     * with ownership as context
     */
    private static Vector<AST> project(Context ctx, Party party, AST stmt) {
        Vector<AST> result = new Vector<>();
        // System.out.printf("project(%s, %s)\n", party.partyVar, stmt.getClass().getSimpleName());
        if (stmt instanceof AST.All) {
            AST.All e = (AST.All) stmt;
            if (exprRole(e.exp, party)) {
                // same role, so lose the quantifier
                result.addAll(projectAll(ctx, party, e.Do));
            } else {
                // different role, keep quantifier
                AST.All e1 = newAll(e);
                e1.Do = projectAll(ctx, party, e.Do);
                result.add(e1);
            }
//        } else if (stmt instanceof AST.Either) {
//            AST.Either e = (AST.Either) stmt;
//            AST.Either e1 = new AST.Either();
//            e1.ors = projectAll(ownership, party, e.ors);
//            return e1;
        } else if (stmt instanceof AST.LabelEither) {
            AST.LabelEither e = (AST.LabelEither) stmt;
            AST.LabelEither e1 = newEither(e);
            e1.clauses = projectAll(ctx, party, e.clauses);
            result.add(e1);
        } else if (stmt instanceof AST.Par) {
            AST.Par e = (AST.Par) stmt;
            AST.Par e1 = newPar(e);
            e1.clauses = projectAll(ctx, party, e.clauses);
            result.add(e1);
        } else if (stmt instanceof AST.Task) {
            AST.Task task = (AST.Task) stmt;
//            boolean thisParty = cancellations.get(task.label).task.equals(party.partyVar);
            boolean thisParty = Printer.show(task.partyId).equals(party.partyVar);
            if (thisParty) {
                AST.Task e1 = newTask(task);
                e1.Do = projectAll(ctx, party, task.Do);
                result.add(e1);
            } else {
//                AST.Skip e2 = new AST.Skip();
//                e2.setOrigin(stmt.getOrigin());
                result.addAll(projectAll(ctx, party, task.Do));
            }
//        } else if (stmt instanceof AST.With) {
            // TODO
        } else if (stmt instanceof AST.LabelIf) {
            AST.LabelIf e = (AST.LabelIf) stmt;
            // TODO check if test expressions all reside on same party
            AST.LabelIf e1 = newIf(e);
            e1.unlabElse = projectAll(ctx, party, e.unlabElse);
            e1.unlabThen = projectAll(ctx, party, e.unlabThen);
            e1.labElse = projectAll(ctx, party, e.labElse);
            e1.labThen = projectAll(ctx, party, e.labThen);
            result.add(e1);
        } else if (stmt instanceof AST.When) {
            AST.When e = (AST.When) stmt;
//            AST.When e1 = new AST.When();
//            copyInto(e1, e);
            // TODO check if test expressions all reside on same party
            result.add(e);
        } else if (stmt instanceof AST.Clause) {
            AST.Clause e = (AST.Clause) stmt;
            AST.Clause e1 = newClause(e);
            e1.labOr = projectAll(ctx, party, e.labOr);
            e1.unlabOr = projectAll(ctx, party, e.unlabOr);
            result.add(e1);
        } else if (stmt instanceof AST.Assign) {
            AST.Assign e = (AST.Assign) stmt;
            AST.Assign e1 = new AST.Assign();
            e1.ass = new Vector<>(((Vector<AST>) projectAll(ctx, party, e.ass)).stream()
                    // projection may create skips here; in that case drop those nodes
                    .filter(sa -> sa instanceof AST.SingleAssign)
                    .collect(Collectors.toList()));
            if (e1.ass.isEmpty()) {
                AST.Skip e2 = new AST.Skip();
                e2.setOrigin(e.getOrigin());
                result.add(e2);
            } else {
                copyInto(e1, e);
                result.add(e1);
            }
        } else if (stmt instanceof AST.SingleAssign) {
            AST.SingleAssign e = (AST.SingleAssign) stmt;
            AST.Lhs lhs = e.lhs;

            // TODO check the rhs uses only expressions available on this party

            // try locals first
            Optional<AST.VarDecl> first = party.localVars.stream().filter(v -> v.var.equals(lhs.var)).findFirst();
            if (first.isPresent()) {
                result.add(e);
            } else {
                // try globals
                Optional<AST.VarDecl> global = ctx.globals.stream().filter(v -> v.var.equals(lhs.var)).findFirst();
                if (global.isPresent()) {
                    result.add(e);
                } else {
                    // this assignment must not involve this party
                    AST.Skip e1 = new AST.Skip();
                    // AST.Assert e1 = new AST.Assert();
                    // e1.exp = tlaExpr("TRUE");
                    copyInto(e1, e);
                    result.add(e1);
                }
            }
        } else if (stmt instanceof AST.Cancel) {
            AST.Cancel e = (AST.Cancel) stmt;
            AST e1;
            if (party.partyVar.equals(ctx.taskOwnership.get(e.task).partyVar)) {
                AST.Cancel e2 = new AST.Cancel();
                e2.task = e.task;
                e1 = e2;
            } else {
                e1 = new AST.Skip();
            }
            copyInto(e1, e);
            result.add(e1);
        } else if (stmt instanceof AST.While) {

            int index = -1;
            for (int i = 0; i < ctx.partiesOrdered.size(); i++) {
                if (ctx.partiesOrdered.get(i).partyVar.equals(party.partyVar)) {
                    index = i;
                }
            }
            if (index == -1) {
                fail("party not found?");
            }

            AST.While w = (AST.While) stmt;

            TLAExpr cond = index == 0 ? w.test : w.extraTests.get(index - 1);
            AST.While w1 = newWhile(w);
            w1.test = cond;
            w1.extraTests = new ArrayList<>();
            w1.unlabDo = projectAll(ctx, party, w1.unlabDo);
            w1.labDo = projectAll(ctx, party, w1.labDo);
            result.add(w1);
        } else if (stmt instanceof AST.MacroCall && ((AST.MacroCall) stmt).name.equals("Send")) {
            String sender = ithMacroArgAsVar((AST.MacroCall) stmt, 0);
            String receiver = ithMacroArgAsVar((AST.MacroCall) stmt, 1);
            boolean isSend = ctx.ownership.get(sender).partyVar.equals(party.partyVar);
            boolean isRecv = ctx.ownership.get(receiver).partyVar.equals(party.partyVar);
            // expand to user-provided macros
            if (isSend) {
                AST.MacroCall send = new AST.MacroCall();
                send.setOrigin(stmt.getOrigin());
                send.name = "Send";
                send.args = new Vector<TLAExpr>();
                send.args.add(((AST.MacroCall) stmt).args.get(1));
                // TODO use tlaExpr
                TLAExpr e = new TLAExpr();
                e.tokens = new Vector<>(); // lines
                e.tokens.add(new Vector<>()); // add a line
                e.addToken(new TLAToken("self", 0, TLAToken.IDENT, 0));
                send.args.add(e);
                send.args.add(((AST.MacroCall) stmt).args.get(2));
                result.add(send);
            } else if (isRecv) {
                AST.MacroCall recv = new AST.MacroCall();
                recv.setOrigin(stmt.getOrigin());
                recv.name = "Receive";
                recv.args = new Vector<TLAExpr>();
                recv.args.add(((AST.MacroCall) stmt).args.get(0));
                // TODO use tlaExpr
                TLAExpr e = new TLAExpr();
                e.tokens = new Vector<>(); // lines
                e.tokens.add(new Vector<>()); // add a line
                e.addToken(new TLAToken("self", 0, TLAToken.IDENT, 0));
                recv.args.add(e);
                recv.args.add(((AST.MacroCall) stmt).args.get(2));
                result.add(recv);
            } else {
                // TODO self-send
                fail("TODO self-send");
            }
        } else {
            fail("unimplemented project(Party, AST) " + stmt);
        }
        return result;
    }

    private static AST.Task newTask(AST.Task task) {
        AST.Task e1 = new AST.Task();
        e1.taskId = task.taskId;
        e1.partyId = task.partyId;
        e1.Do = task.Do;
        copyInto(e1, task);
        return e1;
    }

    private static Vector<AST> transformCancellations(Vector<AST> stmts) {
        return stmts.stream()
                .map(PlusCalExtensions::transformCancellations)
                .collect(Collectors.toCollection(Vector::new));
    }


    private static AST transformCancellations(AST stmt) {
        if (stmt instanceof AST.All) {
            AST.All e = (AST.All) stmt;
            AST.All e1 = newAll(e);
            e1.Do = transformCancellations(e.Do);
            return e1;
        } else if (stmt instanceof AST.LabelEither) {
            AST.LabelEither e = (AST.LabelEither) stmt;
            AST.LabelEither e1 = newEither(e);
            e1.clauses = transformCancellations(e.clauses);
            return e1;
        } else if (stmt instanceof AST.Par) {
            AST.Par e = (AST.Par) stmt;
            AST.Par e1 = newPar(e);
            e1.clauses = transformCancellations(e.clauses);
            return e1;
        } else if (stmt instanceof AST.LabelIf) {
            AST.LabelIf e = (AST.LabelIf) stmt;
            AST.LabelIf e1 = newIf(e);
            e1.unlabElse = transformCancellations(e.unlabElse);
            e1.unlabThen = transformCancellations(e.unlabThen);
            e1.labElse = transformCancellations(e.labElse);
            e1.labThen = transformCancellations(e.labThen);
            return e1;
        } else if (stmt instanceof AST.When) {
            return stmt;
        } else if (stmt instanceof AST.With) {
            AST.With e = (AST.With) stmt;
            AST.With e1 = newWith(e);
            e1.Do = transformCancellations(e.Do);
            return e1;
        } else if (stmt instanceof AST.Task) {
            AST.Task e = (AST.Task) stmt;
            AST.Task e1 = newTask(e);
            e1.Do = transformCancellations(e.Do);
            return e1;
        } else if (stmt instanceof AST.While) {
            AST.While e = (AST.While) stmt;
            AST.While e1 = newWhile(e);
            e1.unlabDo = transformCancellations(e.unlabDo);
            e1.labDo = transformCancellations(e.labDo);
            return e1;
        } else if (stmt instanceof AST.Clause) {
            AST.Clause e = (AST.Clause) stmt;
            AST.Clause e1 = newClause(e);
            e1.labOr = transformCancellations(e.labOr);
            e1.unlabOr = transformCancellations(e.unlabOr);
            return e1;
        } else if (stmt instanceof AST.Assign) {
            return stmt;
        } else if (stmt instanceof AST.Skip) {
            return stmt;
        } else if (stmt instanceof AST.SingleAssign) {
            return stmt;
        } else if (stmt instanceof AST.Cancel) {
            AST.Assign assign = new AST.Assign();
            assign.ass = new Vector<AST>();
            AST.SingleAssign singleAssign = new AST.SingleAssign();
            {
                String lbl = ((AST.Cancel) stmt).task;
//                AST.Lhs lhs = new AST.Lhs();
                {
                    singleAssign.lhs.var = String.format("cancelled_%s", lbl);
                    singleAssign.lhs.setOrigin(stmt.getOrigin());
                    singleAssign.lhs.sub = PcalTranslate.MakeExpr(new Vector());
                }
//                singleAssign.lhs = lhs;
                singleAssign.rhs = tlaExpr("TRUE");
                singleAssign.setOrigin(stmt.getOrigin());
            }
            assign.ass.add(singleAssign);
            assign.setOrigin(stmt.getOrigin());
            return assign;
        } else if (stmt instanceof AST.MacroCall) {
            return stmt;
        } else {
            fail("transformCancellations: unimplemented " + stmt);
            return null;
        }
    }

    private static AST.Clause newClause(AST.Clause e) {
        AST.Clause e1 = new AST.Clause();
        e1.labOr = e.labOr;
        e1.unlabOr = e.unlabOr;
        copyInto(e1, e);
        return e1;
    }

    private static AST.With newWith(AST.With e) {
        AST.With e1 = new AST.With();
        e1.var = e.var;
        e1.Do = e.Do;
        copyInto(e1, e);
        return e1;
    }

    private static AST.When newWhen(AST.When e) {
        AST.When e1 = new AST.When();
        e1.exp = e.exp;
        copyInto(e1, e);
        return e1;
    }

    private static AST.LabelIf newIf(AST.LabelIf e) {
        AST.LabelIf e1 = new AST.LabelIf();
        e1.test = e.test;
        e1.labThen = e.labThen;
        e1.labElse = e.labElse;
        e1.unlabThen = e.unlabThen;
        e1.unlabElse = e.unlabElse;
        copyInto(e1, e);
        return e1;
    }

    private static AST.All newAll(AST.All e) {
        AST.All e1 = new AST.All();
        e1.var = e.var;
        e1.isEq = e.isEq;
        e1.exp = e.exp;
        e1.Do = e.Do;
        copyInto(e1, e);
        return e1;
    }

    private static AST.While newWhile(AST.While e) {
        AST.While e1 = new AST.While();
        e1.test = e.test;
        e1.extraTests = e.extraTests;
        e1.unlabDo = e.unlabDo;
        e1.labDo = e.labDo;
        copyInto(e1, e);
        return e1;
    }

    /**
     * To simplify recursive calls
     */
    private static Vector<AST> projectAll(Context ctx, Party party, Vector<AST> all) {
        return all.stream()
                .flatMap(s -> project(ctx, party, s).stream())
                .collect(Collectors.toCollection(Vector::new));
    }

    private static String ithMacroArgAsVar(AST.MacroCall stmt, int i) {
        TLAExpr e = (TLAExpr) stmt.args.get(i);
        return tlaExprAsVar(e);
    }

    private static String tlaExprAsVar(TLAExpr o) {
        TLAToken o1 = ((Vector<TLAToken>) o.tokens.get(0)).get(0);
        return o1.string;
    }
}
