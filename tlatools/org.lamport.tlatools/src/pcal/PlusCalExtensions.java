package pcal;

import pcal.exception.ParseAlgorithmException;
import pcal.exception.TokenizerException;
import tlc2.mbtc.Pair;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static pcal.ParseAlgorithm.*;

public class PlusCalExtensions {

    private static class Role {
        final String partyVar;
        final boolean equalOrIn;
        final TLAExpr partySet;

        final List<AST.VarDecl> localVars;

        private Role(String partyVar, boolean equalOrIn, TLAExpr partySet, List<AST.VarDecl> localVars) {
            this.partyVar = partyVar;
            this.equalOrIn = equalOrIn;
            this.partySet = partySet;
            this.localVars = localVars;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Role role = (Role) o;
            return equalOrIn == role.equalOrIn && Objects.equals(partyVar, role.partyVar) && Objects.equals(partySet, role.partySet) && Objects.equals(localVars, role.localVars);
        }

        @Override
        public int hashCode() {
            return Objects.hash(partyVar, equalOrIn, partySet, localVars);
        }

        @Override
        public String toString() {
            return "Party{" +
                    "partyVar='" + partyVar + '\'' +
                    ", equalOrIn=" + equalOrIn +
                    ", partySet=" + partySet +
                    ", localVars=" + localVars +
                    '}';
        }
    }

    static class Context {

        // task id -> Party
        Map<String, Role> taskOwnership;

        // TODO remove
        Map<String, AST.Cancel> cancellations;

        Vector<AST.VarDecl> globals;

        // party task id variable -> party
        Map<String, Role> roleDecls;

        // variable -> party
        // deprecated?
        Map<String, Role> ownership;

        // For things like while, which use positional expressions for parties
        List<Role> partiesOrdered;

        // Relations from the paper
        // expression -> role
        Map<String, Role> role;
        // expression -> role
        Map<String, Role> party;
        // loc is stored in party decl

        // bound variables in scope
        Set<String> binders;
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
        ctx.roleDecls = new HashMap<>();
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
            Role role = new Role(partyVar, eqOrIn, partySet, localVars);
            ctx.roleDecls.put(partyVar, role);
            ctx.partiesOrdered.add(role);
            if (eqOrIn) { // is equal
                // add constant exprs to ownership
                ctx.ownership.put(tlaExprAsVar(partySet), role);
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
        ctx.role = new HashMap<>();
        ctx.party = new HashMap<>();
        ctx.roleDecls.values().forEach(r -> {
//            r.localVars.forEach(v -> {
//                ctx.role.put(v.var, r);
//            });
            ctx.role.put(Printer.show(r.partySet), r);
        });
        ctx.ownership.putAll(computeOwnership(ctx, stmts));
        ctx.binders = new HashSet<>();

        stmts = implicitlyQualify(stmts, ctx);

        Map<Role, AST.Process> projected = project(ctx, stmts);

        boolean normalize = true;
//        boolean normalize = false;
        if (normalize) {
            projected = projected.entrySet().stream()
                    .collect(Collectors.toMap(e -> e.getKey(),
                            e -> normalize(e.getValue())));
        }

        projected.entrySet().stream()
                .sorted(Comparator.comparing(e -> e.getKey().partyVar)) // det
                .forEach(e -> System.out.printf("Projection of %s:\n\n%s\n\n",
                        Printer.show(e.getKey().partySet),
                        Printer.show(e.getValue())));

        // do this before translating other constructs, which insert self in the case of stuff like par and all
        projected = renameSelfToMe(projected);

        // Post-projection elaboration
        List<AST.Process> res1 = projected.entrySet().stream()
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

    /**
     * Why do this? self may not refer to the current party any more.
     */
    private static Map<Role, AST.Process> renameSelfToMe(Map<Role, AST.Process> projected) {
        return projected.entrySet()
                .stream()
                .map(e -> {
                    AST.Process v = flatMapProcessBody(e.getValue(),
                            body -> Stream.of(subst("self", "Tail(self)", body)));
                    return new AbstractMap.SimpleEntry<>(e.getKey(), v);
                })
                .collect(Collectors.toMap(e -> e.getKey(), e -> e.getValue()));
    }

    private static Vector<AST> implicitlyQualify(Vector<AST> stmts, Context ctx) {
        return stmts.stream()
                .map(s -> implicitlyQualify(s, ctx))
                .collect(Collectors.toCollection(Vector::new));
    }

    private static TLAExpr implicitlyQualify(TLAExpr e, Context ctx) {
        Vector<Vector<TLAToken>> tokens = e.tokens;
        Vector<String> copy = new Vector<>();
        for (Vector<TLAToken> b : tokens) {
            for (TLAToken s : b) {
                if (s.type == TLAToken.IDENT) {
                    copy.add(s.string);
                    whatToQualifyWith(ctx, s.string).ifPresent(q -> {
                        copy.add("[");
                        copy.add(q);
                        copy.add("]");
                    });
                } else {
                    copy.add(s.string);
                }
            }
        }
        TLAExpr res = tlaExpr(copy.stream().collect(Collectors.joining()));
        return res;
    }

    private static AST implicitlyQualify(AST stmt, Context ctx) {
        if (stmt instanceof AST.All) {
            String v = ((AST.All) stmt).var;
            ctx.binders.add(v);
            AST.All all = newAll((AST.All) stmt);
            all.Do = implicitlyQualify((Vector<AST>) ((AST.All) stmt).Do, ctx);
            // this is correct only if there is no aliasing, which is ok to ensure for models
            ctx.binders.remove(v);
            return all;
        } else if (stmt instanceof AST.Clause) {
            AST.Clause clause = newClause((AST.Clause) stmt);
            if (clause.unlabOr != null) {
                clause.unlabOr = ((Vector<AST>) clause.unlabOr).stream()
                        .map(c -> implicitlyQualify(c, ctx))
                        .collect(Collectors.toCollection(Vector::new));
            } else {
                clause.labOr = ((Vector<AST>) clause.labOr).stream()
                        .map(c -> implicitlyQualify(c, ctx))
                        .collect(Collectors.toCollection(Vector::new));
            }
            return clause;
        } else if (stmt instanceof AST.LabelIf) {
            AST.LabelIf ei = newIf((AST.LabelIf) stmt);
            if (ei.unlabThen != null) {
                ei.unlabThen = ((Vector<AST>) ei.unlabThen).stream()
                        .map(c -> implicitlyQualify(c, ctx))
                        .collect(Collectors.toCollection(Vector::new));
                ei.unlabElse = ((Vector<AST>) ei.unlabElse).stream()
                        .map(c -> implicitlyQualify(c, ctx))
                        .collect(Collectors.toCollection(Vector::new));
            } else {
                ei.labThen = ((Vector<AST>) ei.labThen).stream()
                        .map(c -> implicitlyQualify(c, ctx))
                        .collect(Collectors.toCollection(Vector::new));
                ei.labElse = ((Vector<AST>) ei.labElse).stream()
                        .map(c -> implicitlyQualify(c, ctx))
                        .collect(Collectors.toCollection(Vector::new));
            }
            return ei;
        } else if (stmt instanceof AST.Par) {
            AST.Par par = newPar((AST.Par) stmt);
            par.clauses = ((Vector<AST.Clause>) par.clauses).stream()
                    .map(a -> implicitlyQualify(a, ctx))
                    .collect(Collectors.toCollection(Vector::new));
            return par;
        } else if (stmt instanceof AST.LabelEither) {
            AST.LabelEither ei = newEither((AST.LabelEither) stmt);
            ei.clauses = ((Vector<AST.Clause>) ei.clauses).stream()
                    .map(a -> implicitlyQualify(a, ctx))
                    .collect(Collectors.toCollection(Vector::new));
            return ei;
        } else if (stmt instanceof AST.MacroCall) {
            AST.MacroCall call = newMacroCall((AST.MacroCall) stmt);
            call.args = ((Vector<TLAExpr>) call.args).stream()
                    .map(a -> implicitlyQualify(a, ctx))
                    .collect(Collectors.toCollection(Vector::new));
            return call;
        } else if (stmt instanceof AST.Cancel ||
                stmt instanceof AST.Skip) {
            return stmt;
        } else if (stmt instanceof AST.Task) {
            AST.Task task = newTask((AST.Task) stmt);
            task.Do = ((Vector<AST>) task.Do).stream()
                    .map(a -> implicitlyQualify(a, ctx))
                    .collect(Collectors.toCollection(Vector::new));
            return task;
        } else if (stmt instanceof AST.Assign) {
            AST.Assign assign = newAssign((AST.Assign) stmt);
            assign.ass = ((Vector<AST.SingleAssign>) assign.ass).stream()
                    .map(a -> {
                        AST.SingleAssign a1 = newSingleAssign(a);
                        a1.lhs.sub = whatToQualifyWith(ctx, a1.lhs.var)
                                .map(b -> tlaExpr("[%s]", b))
                                .orElse(a1.lhs.sub);
                        a1.rhs = implicitlyQualify(a.rhs, ctx);
                        return a1;
                    })
                    .collect(Collectors.toCollection(Vector::new));
            return assign;
        } else {
            throw new IllegalArgumentException("implicitlyQualify: unimplemented " + stmt.getClass().getSimpleName());
        }
    }

    /**
     * What to qualify a variable with.
     * If the variable is from a particular role, identify an enclosing binder that should be used to qualify it.
     * If there isn't exactly one, fail.
     * (none: meaningless, as no party is acting;
     * more than one is ambiguous, in which case the user should qualify)
     * If the variable is bound by all, leave it.
     */
    private static Optional<String> whatToQualifyWith(Context ctx, String var) {
        List<Role> possibleRoles = ctx.roleDecls.entrySet().stream()
                .filter(e -> e.getValue().localVars.stream().anyMatch(l -> l.var.equals(var)))
                .map(e -> e.getValue())
                .collect(Collectors.toList());
        if (possibleRoles.isEmpty()) {
            return Optional.empty();
        } else if (possibleRoles.size() > 1) {
            fail(String.format("local variable %s belongs to more than one role?", var));
        }
        Role role = possibleRoles.get(0);
        List<String> bound = ctx.binders.stream().filter(b -> ctx.party.get(b) == role)
                .collect(Collectors.toList());
        if (bound.size() > 1) {
            fail(String.format("more than one binder %s", bound));
        } else if (bound.isEmpty()) {
            return Optional.empty();
        }
        return Optional.of(bound.get(0));
    }

    private static void findTasks(Context ctx, Map<String, Role> tasks, Vector<AST> stmts) {
        stmts.forEach(s -> findTasks(ctx, tasks, s));
    }

    private static void findTasks(Context ctx, Map<String, Role> res, AST stmt) {
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
            res.put(task.taskId, ctx.roleDecls.get(Printer.show(task.partyId)));
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
        e1.clauses = e.clauses;
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
            AST.Clause e1 = newClause(e);
            if (e1.unlabOr != null) {
                e1.unlabOr = ((Stream<AST>) transformTask(e.unlabOr, task)).collect(Collectors.toCollection(Vector::new));
            } else {
                e1.labOr = ((Stream<AST>) transformTask(e.labOr, task)).collect(Collectors.toCollection(Vector::new));
            }
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
    private static List<AST.Process> expandParStatement(Role which, AST.Process proc) {
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

    private static List<AST.Process> expandAllStatement(Role role, AST.Process proc) {
        return transformProcessBody(proc, s -> expandAllStatement(role, s));
    }

    private static AST.Process createProcess(String name, boolean isEq, TLAExpr id,
                                             Vector<AST> body, Vector<AST.VarDecl> decls) {
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
        wait.exp = tlaExpr("pc[Tail(self)] = \"%s\"", label);
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
    private static AST.Process allStatementProcess(Role role, String label,
                                                   String q, TLAExpr qs, Vector<AST> body) {
        AST.When await = new AST.When();
        await.exp = tlaExpr("pc[Tail(self)] = \"%s\"", label);
        await.setOrigin(qs.getOrigin());

        Vector<AST> body1 = new Vector<>();
        body1.add(await);
        body1.addAll(body);

        TLAExpr product = tlaExpr("(%s \\X %s)", qs, role.partySet);
        return createProcess(fresh("proc"), false, product, body1, new Vector<>());
    }

    /**
     * Called for each statement of a process, which may generate more processes
     */
    private static WithProc<AST> expandParStatement(Role which, AST stmt) {
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
                TLAExpr set = tlaExpr("(%s \\X {%s})", id, which.partySet);

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
            wait.exp = tlaExpr("\\A %s \\in ({%s} \\X {%s}) : pc[%s] = \"Done\"", var, tids, which.partySet, var);
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
        } else if (stmt instanceof AST.LabelIf) {
            AST.LabelIf task = (AST.LabelIf) stmt;
            WithProc<Vector<AST>> c1 = expandParStatement(which, (Vector<AST>) task.labThen);
            WithProc<Vector<AST>> c2 = expandParStatement(which, (Vector<AST>) task.labElse);
            WithProc<Vector<AST>> c3 = expandParStatement(which, (Vector<AST>) task.unlabThen);
            WithProc<Vector<AST>> c4 = expandParStatement(which, (Vector<AST>) task.unlabElse);

            AST.LabelIf t1 = newIf(task);
            t1.labThen = c1.thing;
            t1.labElse = c2.thing;
            t1.unlabThen = c3.thing;
            t1.unlabElse = c4.thing;

            List<AST.Process> procs = new ArrayList<>();
            procs.addAll(c1.procs);
            procs.addAll(c2.procs);
            procs.addAll(c3.procs);
            procs.addAll(c4.procs);

            return new WithProc<>(t1, procs);

        } else if (stmt instanceof AST.LabelEither) {
            AST.LabelEither task = (AST.LabelEither) stmt;
            return expandParStatement(which, (Vector<AST>) task.clauses).map(c -> {
                AST.LabelEither t1 = newEither(task);
                t1.clauses = c;
                return t1;
            });
        } else if (stmt instanceof AST.Clause) {
            AST.Clause c = (AST.Clause) stmt;
            if (c.unlabOr != null) {
                return expandParStatement(which, (Vector<AST>) c.unlabOr).map(cl -> {
                    AST.Clause t1 = newClause(c);
                    t1.unlabOr = cl;
                    return t1;
                });
            } else {
                return expandParStatement(which, (Vector<AST>) c.labOr).map(cl -> {
                    AST.Clause t1 = newClause(c);
                    t1.labOr = cl;
                    return t1;
                });
            }
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

    private static WithProc<Vector<AST>> expandParStatement(Role which, Vector<AST> stmt) {
        return WithProc.sequenceV(
                stmt.stream().map(s -> expandParStatement(which, s))
                        .collect(Collectors.toList()));
    }

    // Given an all statement, returns the await statement it is replaced with,
    // together with the process created to support it
    private static WithProc<AST> expandAllStatement(Role role, AST stmt) {
        if (stmt instanceof AST.All) {
            AST.All all = (AST.All) stmt;
            AST.When wait = new AST.When();
            wait.setOrigin(stmt.getOrigin());
            wait.exp = tlaExpr("\\A %s %s (%s \\X %s) : pc[%s] = \"Done\"",
                    all.var, all.isEq ? "=" : "\\in",
                    all.exp, role.partySet,
                    all.var);
            wait.lbl = fresh("fork");

            List<AST.Process> procs = new ArrayList<>();
            return expandAllStatement(role, (Vector<AST>) all.Do).map(d -> {
                // substitute bound variables away
                d = subst(all.var, "Head(self)", d);
                AST.Process proc = allStatementProcess(role, wait.lbl, all.var, all.exp, d);
                procs.add(proc);
                return (AST) wait;
            }).addAll(procs);
        } else if (stmt instanceof AST.Task) {
            AST.Task t = (AST.Task) stmt;
            return expandAllStatement(role, (Vector<AST>) t.Do).map(d -> {
                AST.Task t1 = newTask(t);
                t1.Do = d;
                return t1;
            });
        } else if (stmt instanceof AST.LabelEither) {
            AST.LabelEither t = (AST.LabelEither) stmt;
            return expandAllStatement(role, (Vector<AST>) t.clauses).map(d -> {
                AST.LabelEither t1 = newEither(t);
                t1.clauses = d;
                return t1;
            });
        } else if (stmt instanceof AST.LabelIf) {
            AST.LabelIf task = (AST.LabelIf) stmt;
            WithProc<Vector<AST>> c1 = expandAllStatement(role, (Vector<AST>) task.labThen);
            WithProc<Vector<AST>> c2 = expandAllStatement(role, (Vector<AST>) task.labElse);
            WithProc<Vector<AST>> c3 = expandAllStatement(role, (Vector<AST>) task.unlabThen);
            WithProc<Vector<AST>> c4 = expandAllStatement(role, (Vector<AST>) task.unlabElse);

            AST.LabelIf t1 = newIf(task);
            t1.labThen = c1.thing;
            t1.labElse = c2.thing;
            t1.unlabThen = c3.thing;
            t1.unlabElse = c4.thing;

            List<AST.Process> procs = new ArrayList<>();
            procs.addAll(c1.procs);
            procs.addAll(c2.procs);
            procs.addAll(c3.procs);
            procs.addAll(c4.procs);

            return new WithProc<>(t1, procs);

        } else if (stmt instanceof AST.Clause) {
            AST.Clause t = (AST.Clause) stmt;
            if (t.unlabOr != null) {
                return expandAllStatement(role, (Vector<AST>) t.unlabOr).map(d -> {
                    AST.Clause t1 = newClause(t);
                    t1.unlabOr = d;
                    return t1;
                });
            } else {
                return expandAllStatement(role, (Vector<AST>) t.labOr).map(d -> {
                    AST.Clause t1 = newClause(t);
                    t1.labOr = d;
                    return t1;
                });
            }
        } else if (stmt instanceof AST.While) {
            AST.While t = (AST.While) stmt;
            if (t.unlabDo != null) {
                return expandAllStatement(role, (Vector<AST>) t.unlabDo).map(d -> {
                    AST.While t1 = newWhile(t);
                    t1.unlabDo = d;
                    return t1;
                });
            } else {
                return expandAllStatement(role, (Vector<AST>) t.labDo).map(d -> {
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

    private static WithProc<Vector<AST>> expandAllStatement(Role which, Vector<AST> stmt) {
        return WithProc.sequenceV(
                stmt.stream().map(s -> expandAllStatement(which, s))
                        .collect(Collectors.toList()));
    }

    static Map<String, Role> computeOwnership(Context ctx,
                                              Vector<AST> ast) {
        Map<String, Role> result = new HashMap<>();
        ast.forEach(a -> {
            computeOwnership(ctx, result, a);
        });
        return result;
    }

    static void computeOwnership(Context ctx, Map<String, Role> res, Vector<AST> ast) {
        for (AST ast1 : ast) {
            computeOwnership(ctx, res, ast1);
        }
    }

    static void computeOwnership(Context ctx, Map<String, Role> res, AST ast) {
        if (ast instanceof AST.All) {
            String var = ((AST.All) ast).var;
            TLAExpr exp = ((AST.All) ast).exp;

            Pair<String, Set<String>> setEx = interpretAsSetAndExclusions(exp);

            // build party relation
            Role role = ctx.role.get(setEx._1);
            ctx.party.put(var, role);

            Optional<Role> first = ctx.roleDecls.values().stream()
                    .filter(p -> p.partySet.toString().equals(exp.toString()))
                    .findFirst();
            if (first.isPresent()) {
                res.put(var, first.get());
            } else {
//                fail("non constant set quantified over " + exp);
            }
            computeOwnership(ctx, res, ((AST.All) ast).Do);
        } else if (ast instanceof AST.Task) {
            computeOwnership(ctx, res, ((AST.Task) ast).Do);
        } else if (ast instanceof AST.LabelEither) {
            computeOwnership(ctx, res, ((AST.LabelEither) ast).clauses);
        } else if (ast instanceof AST.Par) {
            computeOwnership(ctx, res, ((AST.Par) ast).clauses);
        } else if (ast instanceof AST.MacroCall && ((AST.MacroCall) ast).name.equals("Transmit")) {
            // nothing
        } else if (ast instanceof AST.MacroCall) {
            // nothing
        } else if (ast instanceof AST.Cancel) {
            // nothing
        } else if (ast instanceof AST.Assign) {
            // nothing
        } else if (ast instanceof AST.When) {
            // nothing
        } else if (ast instanceof AST.Clause) {
            computeOwnership(ctx, res, ((AST.Clause) ast).labOr);
            computeOwnership(ctx, res, ((AST.Clause) ast).unlabOr);
        } else if (ast instanceof AST.LabelIf) {
            computeOwnership(ctx, res, ((AST.LabelIf) ast).unlabElse);
            computeOwnership(ctx, res, ((AST.LabelIf) ast).unlabThen);
            computeOwnership(ctx, res, ((AST.LabelIf) ast).labElse);
            computeOwnership(ctx, res, ((AST.LabelIf) ast).labThen);
        } else if (ast instanceof AST.LabelEither) {
            computeOwnership(ctx, res, ((AST.LabelEither) ast).clauses);
        } else {
            throw new IllegalArgumentException("computeOwnership: unhandled " + ast.getClass().getSimpleName());
        }
    }

    private static void fail(String s) {
        // so this isn't caught and surfaces to the top level
        throw new Error(s);
    }

    private static Map<Role, AST.Process> project(Context ctx, Vector<AST> stmts) {
        return ctx.roleDecls.entrySet().stream().map(e -> {
            Role role = e.getValue();
            Vector<AST> stmts1 = stmts.stream()
                    .flatMap(s -> project(ctx, role, s).stream())
                    .collect(Collectors.toCollection(Vector::new));
            AST.Process process = createProcess(role.partyVar, role.equalOrIn, role.partySet,
                    stmts1, new Vector<>(role.localVars));
            return new AbstractMap.SimpleEntry<>(role, process);
        }).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
    }

    /**
     * Parses a TLAExpr expression of the form: set \ {a, ...}.
     * Sadly we have to resort to this because TLA expressions are represented
     * opaquely at the PlusCal level.
     */
    static Pair<String, Set<String>> interpretAsSetAndExclusions(TLAExpr a) {
        String s = Printer.show(a);
        String[] split = s.split("\\s*\\\\\\s*");
        if (split.length == 1) {
            return new Pair<>(s, new HashSet<>());
        }
        Set<String> elts = Arrays.stream(split[1].split("\\s*[{},]\\s*"))
                .filter(s1 -> !s1.isEmpty())
                .collect(Collectors.toSet());
        return new Pair<>(split[0], elts);
    }

    static TLAExpr addExclusion(TLAExpr a, String v) {
        Pair<String, Set<String>> setEx = interpretAsSetAndExclusions(a);
        Set<String> n = new HashSet<>(setEx._2);
        n.add(v);
        return tlaExpr("%s \\ {%s}", setEx._1, n.stream().collect(Collectors.joining(",")));
    }

    /**
     * sad
     */
    private static TLAExpr subst(String var, String with, TLAExpr in) {
        TLAExpr copy = tlaExpr(Printer.show(in));
        Vector<Vector<TLAToken>> tokens = copy.tokens;
        for (Vector<TLAToken> b : tokens) {
            for (TLAToken s : b) {
                if (s.type == TLAToken.IDENT) {
                    s.string = s.string.replaceAll("^" + var + "$", with);
                }
            }
        }
        return copy;
    }

    private static AST.Lhs subst(String var, String with, AST.Lhs in) {
        AST.Lhs res = new AST.Lhs();
        if (in.var != null && in.var.equals(var)) {
            res.var = with;
        } else {
            res.var = in.var;
        }
        res.sub = subst(var, with, in.sub);
        copyInto(in, res);
        return res;
    }

    private static AST subst(String var, String with, AST in) {
        if (in instanceof AST.All) {
            AST.All a = newAll((AST.All) in);
            if (a.var.equals(var)) {
                a.var = with;
            }
            a.exp = subst(var, with, a.exp);
            a.Do = subst(var, with, a.Do);
            return a;
        } else if (in instanceof AST.Task) {
            AST.Task a = newTask((AST.Task) in);
            a.partyId = subst(var, with, a.partyId);
            a.Do = subst(var, with, a.Do);
            return a;
        } else if (in instanceof AST.Assign) {
            AST.Assign i = newAssign((AST.Assign) in);
            i.ass = ((Vector<AST.SingleAssign>) i.ass).stream()
                    .map(a -> {
                        AST.SingleAssign a1 = newSingleAssign(a);
                        a1.rhs = subst(var, with, a.rhs);
                        a1.lhs = subst(var, with, a.lhs);
                        return a1;
                    })
                    .collect(Collectors.toCollection(Vector::new));
            return i;
        } else if (in instanceof AST.MacroCall) {
            AST.MacroCall i = newMacroCall((AST.MacroCall) in);
            i.args = ((Vector<TLAExpr>) i.args).stream()
                    .map(a -> subst(var, with, a))
                    .collect(Collectors.toCollection(Vector::new));
            return i;
        } else if (in instanceof AST.Skip ||
                in instanceof AST.Cancel) {
            return in;
        } else if (in instanceof AST.LabelEither) {
            AST.LabelEither i = newEither((AST.LabelEither) in);
            i.clauses = ((Vector<AST>) i.clauses).stream()
                    .map(c -> subst(var, with, c))
                    .collect(Collectors.toCollection(Vector::new));
            return i;
        } else if (in instanceof AST.Par) {
            AST.Par i = newPar((AST.Par) in);
            i.clauses = ((Vector<AST>) i.clauses).stream()
                    .map(c -> subst(var, with, c))
                    .collect(Collectors.toCollection(Vector::new));
            return i;
        } else if (in instanceof AST.LabelIf) {
            AST.LabelIf i = newIf((AST.LabelIf) in);
            if (i.unlabThen != null) {
                i.unlabThen = ((Vector<AST>) i.unlabThen).stream()
                        .map(c -> subst(var, with, c))
                        .collect(Collectors.toCollection(Vector::new));
                i.unlabElse = ((Vector<AST>) i.unlabElse).stream()
                        .map(c -> subst(var, with, c))
                        .collect(Collectors.toCollection(Vector::new));
            } else {
                i.labThen = ((Vector<AST>) i.labThen).stream()
                        .map(c -> subst(var, with, c))
                        .collect(Collectors.toCollection(Vector::new));
                i.labElse = ((Vector<AST>) i.labElse).stream()
                        .map(c -> subst(var, with, c))
                        .collect(Collectors.toCollection(Vector::new));
            }
            return i;
        } else if (in instanceof AST.Clause) {
            AST.Clause i = newClause((AST.Clause) in);
            if (i.unlabOr != null) {
                i.unlabOr = ((Vector<AST>) i.unlabOr).stream()
                        .map(c -> subst(var, with, c))
                        .collect(Collectors.toCollection(Vector::new));
            } else {
                i.labOr = ((Vector<AST>) i.labOr).stream()
                        .map(c -> subst(var, with, c))
                        .collect(Collectors.toCollection(Vector::new));
            }
            return i;
        } else {
            throw new IllegalArgumentException("subst: unimplemented " + in.getClass().getSimpleName());
        }
    }

    private static Vector<AST> subst(String var, String with, Vector<AST> stmts) {
        return stmts.stream().map(s -> subst(var, with, s))
                .collect(Collectors.toCollection(Vector::new));
    }

    private static Vector<AST> normalizeStep(AST in) {
        Vector<AST> result = new Vector<>();
        if (in instanceof AST.All) {
            AST.All a = (AST.All) in;
            Vector<AST> stmts = ((Vector<AST>) a.Do).stream()
                    .filter(b -> !(b instanceof AST.Skip))
                    .collect(Collectors.toCollection(Vector::new));
            if (stmts.isEmpty()) {
                AST.Skip skip = new AST.Skip();
                skip.setOrigin(in.getOrigin());
                result.add(skip);
            } else {
                AST.All a1 = newAll(a);
                a1.Do = normalizeStep(stmts);
                result.add(a1);
            }
        } else if (in instanceof AST.LabelEither) {
            AST.LabelEither a = (AST.LabelEither) in;
            Vector<AST> clauses = ((Vector<AST>) a.clauses).stream()
                    .flatMap(c -> normalizeStep(c).stream())
                    .filter(c -> {
                        AST.Clause cl = (AST.Clause) c;
                        if (cl.unlabOr != null) {
                            return !cl.unlabOr.isEmpty();
                        } else {
                            return !cl.labOr.isEmpty();
                        }
                    })
                    .collect(Collectors.toCollection(Vector::new));
            if (clauses.isEmpty()) {
                AST.Skip skip = new AST.Skip();
                skip.setOrigin(in.getOrigin());
                result.add(skip);
            } else if (clauses.size() == 1) {
                AST.Clause cl = (AST.Clause) clauses.get(0);
                if (cl.unlabOr != null) {
                    result.addAll(cl.unlabOr);
                } else {
                    result.addAll(cl.labOr);
                }
            } else {
                AST.LabelEither a1 = newEither(a);
                a1.clauses = clauses;
                result.add(a1);
            }
        } else if (in instanceof AST.Par) {
            AST.Par a = (AST.Par) in;
            Vector<AST> clauses = ((Vector<AST>) a.clauses).stream()
                    .flatMap(c -> normalizeStep(c).stream())
                    .filter(c -> {
                        AST.Clause cl = (AST.Clause) c;
                        if (cl.unlabOr != null) {
                            return !cl.unlabOr.isEmpty();
                        } else {
                            return !cl.labOr.isEmpty();
                        }
                    })
                    .collect(Collectors.toCollection(Vector::new));
            if (clauses.isEmpty()) {
                AST.Skip skip = new AST.Skip();
                skip.setOrigin(in.getOrigin());
                result.add(skip);
            } else if (clauses.size() == 1) {
                AST.Clause cl = (AST.Clause) clauses.get(0);
                if (cl.unlabOr != null) {
                    result.addAll(cl.unlabOr);
                } else {
                    result.addAll(cl.labOr);
                }
            } else {
                AST.Par a1 = newPar(a);
                a1.clauses = clauses;
                result.add(a1);
            }
        } else if (in instanceof AST.MacroCall ||
                in instanceof AST.Skip ||
                in instanceof AST.Assign ||
                in instanceof AST.Cancel) {
            // nothing
            result.add(in);
        } else if (in instanceof AST.Clause) {
            AST.Clause c = newClause((AST.Clause) in);
            if (c.unlabOr != null) {
                c.unlabOr = normalizeStep((Vector<AST>) c.unlabOr).stream()
                        .filter(b -> !(b instanceof AST.Skip))
                        .collect(Collectors.toCollection(Vector::new));
            } else {
                c.labOr = normalizeStep((Vector<AST>) c.labOr).stream()
                        .filter(b -> !(b instanceof AST.Skip))
                        .collect(Collectors.toCollection(Vector::new));
            }
            result.add(c);
        } else if (in instanceof AST.LabelIf) {
            AST.LabelIf c = newIf((AST.LabelIf) in);
            if (c.unlabThen != null) {
                c.unlabThen = normalizeStep((Vector<AST>) c.unlabThen);
                c.unlabElse = normalizeStep((Vector<AST>) c.unlabElse);
            } else {
                c.labThen = normalizeStep((Vector<AST>) c.labThen);
                c.labElse = normalizeStep((Vector<AST>) c.labElse);
            }
            result.add(c);
        } else if (in instanceof AST.Task) {
            AST.Task c = newTask((AST.Task) in);
            c.Do = normalizeStep((Vector<AST>) c.Do);
            result.add(c);
        } else {
            throw new IllegalArgumentException("normalizeStep: unimplemented " + in.getClass().getSimpleName());
        }
        return result;
    }

    private static Vector<AST> normalizeStep(Vector<AST> stmts) {
        return stmts.stream().flatMap(s -> normalizeStep(s).stream())
                .collect(Collectors.toCollection(Vector::new));
    }

    static AST.Process normalize(AST.Process proc) {

//        boolean debug = true;
        boolean debug = false;

        Vector a = proc.body;
        Vector<AST> a1 = normalizeStep(a);

        if (debug) {
            System.out.println("DEBUG normalize\n---");
            System.out.println(Printer.show(a));
            System.out.println("---");
            System.out.println(Printer.show(a1));
        }

        while (!Printer.show(a).equals(Printer.show(a1))) {
            a = a1;
            a1 = normalizeStep(a);
            if (debug) {
                System.out.println("---");
                System.out.println(Printer.show(a1));
            }
        }
        if (debug) {
            System.out.println("--- fixed point");
        }

        return createProcess(proc.name, proc.isEq, proc.id, a1, proc.decls);
    }

    /**
     * Main projection function, splitting a statement into its local equivalent for the given role,
     * with ownership as context
     */
    private static Vector<AST> project(Context ctx, Role role, AST stmt) {
        Vector<AST> result = new Vector<>();
        // System.out.printf("project(%s, %s)\n", party.partyVar, stmt.getClass().getSimpleName());
        if (stmt instanceof AST.All) {
            AST.All e = (AST.All) stmt;

            Pair<String, Set<String>> setEx = interpretAsSetAndExclusions(e.exp);
            Set<String> excl = setEx._2;

            String ee = Printer.show(e);

            // We use "self" as the name of arbitrary member of role
            if (!excl.contains("self") && ctx.role.get(Printer.show(e.exp)) == role) {
                // self could be inside, so use self-send projection

                Vector<AST> left = projectAll(ctx, role, subst(e.var, "self", e.Do));
                String l = Printer.show(left);

                AST.All right = newAll((AST.All) stmt);
                right.exp = addExclusion(right.exp, "self");
                right.Do = projectAll(ctx, role, right.Do);

                String r = Printer.show(right);

                // build par
                AST.Clause c1 = new AST.Clause();
                c1.setOrigin(stmt.getOrigin());
                c1.unlabOr = new Vector<>();
                c1.unlabOr.addAll(left);

                AST.Clause c2 = new AST.Clause();
                c2.setOrigin(stmt.getOrigin());
                c2.unlabOr = new Vector<>();
                c2.unlabOr.add(right);

                AST.Par par = new AST.Par();
                par.clauses = new Vector<>();
                par.clauses.add(c1);
                par.clauses.add(c2);
                par.setOrigin(stmt.getOrigin());

                result.add(par);
            } else {
                // use homomorphic projection, i.e. keep the quantifier
                AST.All e1 = newAll(e);
                e1.Do = projectAll(ctx, role, e.Do);
                result.add(e1);
            }

//            if (Printer.show(e.exp).contains("\\")) {
//               int a = 1;
//            }
//
//            if (ctx.role.get(Printer.show(e.exp)) == role) {
//                // same role, so lose the quantifier
//                result.addAll(projectAll(ctx, role, e.Do));
//            } else {
//                // different role, keep quantifier
//                AST.All e1 = newAll(e);
//                e1.Do = projectAll(ctx, role, e.Do);
//                result.add(e1);
//            }

//        } else if (stmt instanceof AST.Either) {
//            AST.Either e = (AST.Either) stmt;
//            AST.Either e1 = new AST.Either();
//            e1.ors = projectAll(ownership, party, e.ors);
//            return e1;
        } else if (stmt instanceof AST.LabelEither) {
            AST.LabelEither e = (AST.LabelEither) stmt;
            AST.LabelEither e1 = newEither(e);
            e1.clauses = projectAll(ctx, role, e.clauses);
            result.add(e1);
        } else if (stmt instanceof AST.Par) {
            AST.Par e = (AST.Par) stmt;
            AST.Par e1 = newPar(e);
            e1.clauses = projectAll(ctx, role, e.clauses);
            result.add(e1);
        } else if (stmt instanceof AST.Task) {
            AST.Task task = (AST.Task) stmt;
//            boolean thisParty = cancellations.get(task.label).task.equals(party.partyVar);
            boolean thisParty = Printer.show(task.partyId).equals(role.partyVar);
            if (thisParty) {
                AST.Task e1 = newTask(task);
                e1.Do = projectAll(ctx, role, task.Do);
                result.add(e1);
            } else {
//                AST.Skip e2 = new AST.Skip();
//                e2.setOrigin(stmt.getOrigin());
                result.addAll(projectAll(ctx, role, task.Do));
            }
//        } else if (stmt instanceof AST.With) {
            // TODO
        } else if (stmt instanceof AST.LabelIf) {
            AST.LabelIf e = (AST.LabelIf) stmt;
            // TODO check if test expressions all reside on same party
            AST.LabelIf e1 = newIf(e);
            e1.unlabElse = projectAll(ctx, role, e.unlabElse);
            e1.unlabThen = projectAll(ctx, role, e.unlabThen);
            e1.labElse = projectAll(ctx, role, e.labElse);
            e1.labThen = projectAll(ctx, role, e.labThen);
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
            e1.labOr = projectAll(ctx, role, e.labOr);
            e1.unlabOr = projectAll(ctx, role, e.unlabOr);
            result.add(e1);
        } else if (stmt instanceof AST.Assign) {
            AST.Assign e = (AST.Assign) stmt;
            AST.Assign e1 = new AST.Assign();
            e1.ass = new Vector<>(((Vector<AST>) projectAll(ctx, role, e.ass)).stream()
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
            Optional<AST.VarDecl> first = role.localVars.stream().filter(v -> v.var.equals(lhs.var)).findFirst();
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
            if (role.partyVar.equals(ctx.taskOwnership.get(e.task).partyVar)) {
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
                if (ctx.partiesOrdered.get(i).partyVar.equals(role.partyVar)) {
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
            w1.unlabDo = projectAll(ctx, role, w1.unlabDo);
            w1.labDo = projectAll(ctx, role, w1.labDo);
            result.add(w1);
        } else if (stmt instanceof AST.MacroCall && ((AST.MacroCall) stmt).name.equals("Transmit")) {
            String sender = ithMacroArgAsVar((AST.MacroCall) stmt, 0);
            String receiver = ithMacroArgAsVar((AST.MacroCall) stmt, 1);
            if (sender.equals("self") && sender.equals(receiver)) {
                throw new IllegalArgumentException("invalid projection");
            }
//            boolean isSend = !receiver.equals("self") && (sender.equals("self") || ctx.party.get(sender).partyVar.equals(role.partyVar));
//            boolean isRecv = !sender.equals("self") && (receiver.equals("self") || ctx.party.get(receiver).partyVar.equals(role.partyVar));
            boolean isSend = sender.equals("self");
            boolean isRecv = receiver.equals("self");
            // expand to user-provided macros
            if (isSend) {
                AST.MacroCall send = new AST.MacroCall();
                send.setOrigin(stmt.getOrigin());
                send.name = "Send";
                send.args = new Vector<TLAExpr>();
                send.args.add(tlaExpr("self"));
                send.args.add(((AST.MacroCall) stmt).args.get(1));
                send.args.add(((AST.MacroCall) stmt).args.get(2));
                result.add(send);
            } else if (isRecv) {
                AST.MacroCall recv = new AST.MacroCall();
                recv.setOrigin(stmt.getOrigin());
                recv.name = "Receive";
                recv.args = new Vector<TLAExpr>();
                recv.args.add(((AST.MacroCall) stmt).args.get(0));
                recv.args.add(tlaExpr("self"));
                recv.args.add(((AST.MacroCall) stmt).args.get(2));
                result.add(recv);
            } else {
                AST.Skip skip = new AST.Skip();
                skip.setOrigin(stmt.getOrigin());
                result.add(skip);
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

    private static AST.Cancel newCancel(AST.Cancel cancel) {
        AST.Cancel e1 = new AST.Cancel();
        e1.task = cancel.task;
        copyInto(e1, cancel);
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
            if (e.unlabOr != null) {
                e1.unlabOr = transformCancellations(e.unlabOr);
            } else {
                e1.labOr = transformCancellations(e.labOr);
            }
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

    private static AST.MacroCall newMacroCall(AST.MacroCall e) {
        AST.MacroCall e1 = new AST.MacroCall();
        e1.name = e.name;
        e1.args = new Vector<>(e.args);
        copyInto(e1, e);
        return e1;
    }

    private static AST.Assign newAssign(AST.Assign e) {
        AST.Assign e1 = new AST.Assign();
        e1.ass = new Vector<>(e.ass);
        copyInto(e1, e);
        return e1;
    }

    private static AST.SingleAssign newSingleAssign(AST.SingleAssign e) {
        AST.SingleAssign e1 = new AST.SingleAssign();
        e1.lhs = e.lhs;
        e1.rhs = e.rhs;
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
    private static Vector<AST> projectAll(Context ctx, Role role, Vector<AST> all) {
        return all.stream()
                .flatMap(s -> project(ctx, role, s).stream())
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
