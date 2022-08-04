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

    public static AST GetAll(int depth) throws ParseAlgorithmException {
        return InnerGetAll(depth, null) ;
    }

    /**
     * Just a with statement with different keyword, return type, constructor, error messages.
     * The reason we don't parameterize {@link ParseAlgorithm#InnerGetWith} is that there is no supertype of With/All
     * that has all the fields we need to assign.
     */
    public static AST.All InnerGetAll(int depth, PCalLocation beginLoc) throws ParseAlgorithmException
    {
        PCalLocation begLoc = beginLoc ;
        if (depth == 0)
        { GobbleThis("all") ;
            begLoc = GetLastLocationStart() ;
            if (cSyntax) { GobbleThis("(") ; } ;
        } ;
        AST.All result = new AST.All() ;
        result.col  = lastTokCol ;
        result.line = lastTokLine ;
        result.var  = GetAlgToken() ;
        result.isEq = GobbleEqualOrIf() ;
        result.exp  = GetExpr() ;
        if (pSyntax || ! PeekAtAlgToken(1).equals(")"))
        { GobbleCommaOrSemicolon();
            /**************************************************************
             * Gobble the ";" or "," ending the <VarEqOrIn>, which may be  *
             * eliminated before a ")" or "do".                            *
             **************************************************************/
        } ;
        if (result.exp.tokens.size() == 0)
        { ParsingError("Empty all expression at ") ;} ;
        if (pSyntax && PeekAtAlgToken(1).equals("do"))
        { GobbleThis("do") ;
            result.Do   = GetStmtSeq() ;
            GobbleThis("end") ;
            GobbleThis("all") ;
            GobbleThis(";");
        }
        else if (cSyntax && PeekAtAlgToken(1).equals(")"))
        { MustGobbleThis(")") ;
            result.Do = GetCStmt() ;
        }
        else
        { result.Do = new Vector() ;
            result.Do.addElement(InnerGetAll(depth+1, begLoc)) ;
        };
        try {
            result.setOrigin(new Region(begLoc,
                    ((AST) result.Do.elementAt(result.Do.size()-1)).getOrigin().getEnd())) ;
        } catch (ArrayIndexOutOfBoundsException e) {
            throw new ParseAlgorithmException("Missing body of all statement", result);
        }
        return result ;
    }

    public static AST.Task GetTask() throws ParseAlgorithmException
    {
//        if (depth == 0)
//        {
        GobbleThis("task") ;
        PCalLocation begLoc = GetLastLocationStart() ;
//            if (cSyntax) { GobbleThis("(") ; } ;
//        } ;

        AST.Task result = new AST.Task();
        result.col  = lastTokCol ;
        result.line = lastTokLine ;
        result.label = GetAlgToken() ;
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
        if (pSyntax && PeekAtAlgToken(1).equals("do"))
        { GobbleThis("do") ;
            result.Do   = GetStmtSeq() ;
            GobbleThis("end") ;
//            GobbleThis("all") ;
            GobbleThis("task") ;
            GobbleThis(";");
        }
        else if (cSyntax) // && PeekAtAlgToken(1).equals(")"))
        { //MustGobbleThis(")") ;
            result.Do = GetCStmt() ;
        }
//        else
//        { result.Do = new Vector() ;
//            result.Do.addElement(InnerGetAll(depth+1, begLoc)) ;
//        };
        try {
            result.setOrigin(new Region(begLoc,
                    ((AST) result.Do.elementAt(result.Do.size()-1)).getOrigin().getEnd())) ;
        } catch (ArrayIndexOutOfBoundsException e) {
            throw new ParseAlgorithmException("Missing body of task statement", result);
        }
        return result ;
    }

//    public static Map<String, AST.Cancel> cancellations;

    public static List<AST.Process> GetChoreography(Vector<AST.VarDecl> globals,
                                                    Vector<AST.Macro> macros) throws ParseAlgorithmException {
        GobbleThis("choreography");

        Map<String, Party> partyDecls = new HashMap<>();
        Map<String, Party> ownership = new HashMap<>();

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
            }
            Party party = new Party(partyVar, eqOrIn, partySet, localVars);
            partyDecls.put(partyVar, party);
            if (eqOrIn) {
                // if equal, add constant exprs to ownership
                ownership.put(tlaExprAsVar(partySet), party);
            }
            if (PeekAtAlgToken(1).equals(",")) {
                GobbleThis(",");
            } else {
                break;
            }
        }

        GobbleBeginOrLeftBrace() ;
        Vector<AST> stmts = GetStmtSeq();
        GobbleEndOrRightBrace("choreography") ;

        //////
        // Translate into regular PlusCal
        //////

        // Preprocessing to handle cancellations
        Map<String, AST.Cancel> cancellations = new HashMap<>();
        findCancellations(cancellations, stmts);
        cancellations.forEach((key, value) -> {
            AST.VarDecl v = new AST.VarDecl();
            v.var = String.format("cancelled_%s", key);
            v.val = tlaExpr("FALSE");
            v.isEq = true;
            globals.add(v);
        });
        // don't transform away cancellations until after projection

        // Ownership and projection
        Map<String, Party> quantified = computeOwnership(partyDecls, stmts);
        ownership.putAll(quantified);
        Map<Party, AST.Process> res = project(globals, ownership, partyDecls, cancellations, stmts);

        // Post-projection elaboration
        List<AST.Process> res1 = res.entrySet().stream()
                .flatMap(p -> expandAllStatement(ownership, partyDecls, p.getValue()).stream().map(pr -> new AbstractMap.SimpleEntry<>(p.getKey(), pr)))
                .flatMap(p -> expandParStatement(ownership, partyDecls, p.getKey(), p.getValue()).stream().map(pr -> new AbstractMap.SimpleEntry<>(p.getKey(), pr)))
                .flatMap(p -> expandCancellations(p.getValue()).stream().map(pr -> new AbstractMap.SimpleEntry<>(p.getKey(), pr)))
                .map(Map.Entry::getValue)
                .map(PlusCalExtensions::expandTask)
                .collect(Collectors.toList());

        // TODO optimize, remove the no-op processes entirely

        return res1;
    }

    private static void findCancellations(Map<String, AST.Cancel> res, Vector<AST> stmts) {
        stmts.forEach(s -> findCancellations(res, s));
    }

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
        } else if (stmt instanceof AST.Assign) {
            // nothing
        } else if (stmt instanceof AST.SingleAssign) {
            // nothing
        } else if (stmt instanceof AST.Cancel) {
            res.put(((AST.Cancel) stmt).to, (AST.Cancel) stmt);
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
    }

    /**
     * This is essentially {@link ParseAlgorithm#GetEither()} with the keywords changed
     */
    public static AST.Par  GetPar() throws ParseAlgorithmException
    { MustGobbleThis("par") ;
        PCalLocation beginLoc = GetLastLocationStart() ;
        AST.Par result = new AST.Par() ;
        result.col  = lastTokCol ;
        result.line = lastTokLine ;
        result.clauses = new Vector() ;
        boolean done = false ;
        boolean hasOr = false ;
        while (! done)
        { AST.Clause nextClause = new AST.Clause() ;
            nextClause.labOr = new Vector() ;
            if (pSyntax)
            { nextClause.unlabOr = GetStmtSeq() ; }
            else
            { nextClause.unlabOr = GetCStmt() ; }
            if (nextClause.unlabOr.size() == 0)
            {throw new ParseAlgorithmException(
                    "`par' statement with empty `and' clause", result) ; } ;
            nextClause.setOrigin(new Region(
                    ((AST) nextClause.unlabOr.elementAt(0)).getOrigin().getBegin(),
                    ((AST) nextClause.unlabOr.elementAt(nextClause.unlabOr.size()-1))
                            .getOrigin().getEnd())) ;
            result.clauses.addElement(nextClause) ;
            String nextTok = PeekAtAlgToken(1) ;
            if (nextTok.equals("and"))
            { MustGobbleThis("and") ;
                hasOr = true ;
            }
            else
            { done = true ; }
        } ;
        if (pSyntax)
        { MustGobbleThis("end") ;
            GobbleThis("par") ;
            GobbleThis(";") ;
        } ;
        if (! hasOr)
        { throw new ParseAlgorithmException("`par' statement has no `and'", result) ;
        } ;
        result.setOrigin(new Region(beginLoc,
                ((AST) result.clauses.elementAt(result.clauses.size()-1))
                        .getOrigin().getEnd())) ;
        return result ;
    }

    /**
     * Very similar to {@link ParseAlgorithm#GetGoto()}
     */
    public static AST.Cancel GetCancel() throws ParseAlgorithmException
    { MustGobbleThis("cancel") ;
        AST.Cancel result = new AST.Cancel() ;
        result.col  = lastTokCol ;
        result.line = lastTokLine ;
        result.who   = GetAlgToken() ;
        result.to   = GetAlgToken() ;
        result.setOrigin(new Region(new PCalLocation(result.line-1, result.col-1),
                new PCalLocation(lastTokLine-1, lastTokCol-1+result.to.length()))) ;
        gotoUsed = true ;
        // The translator accepts `goto "Done"' and treats it like
        // `goto Done'.  Testing reveals that the outer
        // parentheses seem to be removed before we get here, but I
        // don't trust my tests, so let's check for both.
        if (result.to.equals("Done") || result.to.equals("\"Done\"")) {
            gotoDoneUsed = true;
        }
        GobbleThis(";") ;
        return result ;
    }

    private static List<AST.Process> expandCancellations(AST.Process proc) {
        return transformProcessBody(proc, s -> new WithProc<>(transformCancellations(s), List.of()));
//        stmts = transformCancellations(stmts);
//        return null;
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

    private static Stream<AST> transformTask(AST stmt, Optional<AST.Task> task) {
        Stream<AST> res;
        if (stmt instanceof AST.All) {
            AST.All e = (AST.All) stmt;
            AST.All e1 = new AST.All();
            e1.var = e.var;
            e1.isEq = e.isEq;
            e1.exp = e.exp;
            e1.Do = ((Stream<AST>) transformTask(e.Do, task)).collect(Collectors.toCollection(Vector::new));
            copyInto(e1, e);
            res = Stream.of(e1);
        } else if (stmt instanceof AST.LabelEither) {
            AST.LabelEither e = (AST.LabelEither) stmt;
            AST.LabelEither e1 = new AST.LabelEither();
            e1.clauses = ((Stream<AST>) transformTask(e.clauses, task)).collect(Collectors.toCollection(Vector::new));
            copyInto(e1, e);
            res = Stream.of(e1);
        } else if (stmt instanceof AST.Par) {
            AST.Par e = (AST.Par) stmt;
            AST.Par e1 = new AST.Par();
            e1.clauses = ((Stream<AST>) transformTask(e.clauses, task)).collect(Collectors.toCollection(Vector::new));
            copyInto(e1, e);
            res = Stream.of(e1);
        } else if (stmt instanceof AST.Task) {
            AST.Task e = (AST.Task) stmt;
            if (e.lbl != null) {
                fail("tasks cannot have labels, as it is unclear how many statements in their body the label should apply to");
            }
            res = ((Stream<AST>) transformTask(e.Do, Optional.of(e)));
//        } else if (stmt instanceof AST.With) {
            // TODO
//            res = Stream.of(e1);
        } else if (stmt instanceof AST.LabelIf) {
            AST.LabelIf e = (AST.LabelIf) stmt;
            AST.LabelIf e1 = new AST.LabelIf();
            e1.test = e.test;
            e1.labElse = ((Stream<AST>) transformTask(e.labElse, task)).collect(Collectors.toCollection(Vector::new));
            e1.labThen = ((Stream<AST>) transformTask(e.labThen, task)).collect(Collectors.toCollection(Vector::new));
            e1.unlabElse = ((Stream<AST>) transformTask(e.unlabElse, task)).collect(Collectors.toCollection(Vector::new));
            e1.unlabThen = ((Stream<AST>) transformTask(e.unlabThen, task)).collect(Collectors.toCollection(Vector::new));
            copyInto(e1, e);
            res = Stream.of(e1);
        } else if (stmt instanceof AST.Clause) {
            AST.Clause e = (AST.Clause) stmt;
            AST.Clause e1 = new AST.Clause();
            e1.labOr = ((Stream<AST>) transformTask(e.labOr, task)).collect(Collectors.toCollection(Vector::new));
            e1.unlabOr = ((Stream<AST>) transformTask(e.unlabOr, task)).collect(Collectors.toCollection(Vector::new));
            copyInto(e1, e);
            res = Stream.of(e1);
        } else if (stmt instanceof AST.When) {
            res = Stream.of(stmt);
        } else if (stmt instanceof AST.Assign) {
            res = Stream.of(stmt);
        } else if (stmt instanceof AST.SingleAssign) {
            res = Stream.of(stmt);
        } else if (stmt instanceof AST.Cancel) {
            res = Stream.of(stmt);
        } else if (stmt instanceof AST.MacroCall) {
            res = Stream.of(stmt);
        } else if (stmt instanceof AST.Skip) {
            res = Stream.of(stmt);
        } else {
            fail("unimplemented transformTask(Party, AST) " + stmt);
            return null;
        }
        if (task.isEmpty()) {
            return res;
        } else {
            AST.When guard = convertTask(task.get());
            return Stream.concat(Stream.of(guard), res);
        }
    }

    private static Stream<AST> transformTask(Vector<AST> s, Optional<AST.Task> task) {
        return s.stream().flatMap(s1 -> transformTask(s1, task));
    }

    /**
     * Expand occurrences of par statements in a process
     */
    private static List<AST.Process> expandParStatement(Map<String, Party> ownership,
                                                        Map<String, Party> partyDecls,
                                                        Party which,
                                                        AST.Process proc) {
        return transformProcessBody(proc, s -> expandParStatement(ownership, partyDecls, which, s));
////         TODO this is the same as expandAllStatement except for the function passed to map here
//        List<WithProc<AST>> res = ((Vector<AST>) proc.body).stream()
//                .map()
//                .collect(Collectors.toList());
//
//        List<AST> body1 = res.stream()
//                .map(wp -> wp.thing)
//                .collect(Collectors.toList());
//        AST.Process proc1 = createProcess(proc.name, proc.isEq, proc.id, new Vector<>(body1), proc.decls);
//
//        List<AST.Process> newProcesses = res.stream()
//                .flatMap(wp -> wp.procs.stream())
//                .collect(Collectors.toCollection(ArrayList::new));
//
//        newProcesses.add(proc1);
//
//        return newProcesses;
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

    private static List<AST.Process> expandAllStatement(Map<String, Party> ownership,
                                                        Map<String, Party> partyDecls,
                                                        AST.Process proc) {
        return transformProcessBody(proc, s -> expandAllStatement(ownership, partyDecls, s));

//        List<WithProc<AST>> res = ((Vector<AST>) proc.body).stream()
//                .map(s -> expandAllStatement(ownership, partyDecls, s))
//                .collect(Collectors.toList());
//
//        List<AST> body1 = res.stream()
//                .map(wp -> wp.thing)
//                .collect(Collectors.toList());
//        AST.Process proc1 = createProcess(proc.name, proc.isEq, proc.id, new Vector<>(body1), proc.decls);
//
//        List<AST.Process> newProcesses = res.stream()
//                .flatMap(wp -> wp.procs.stream())
//                .collect(Collectors.toCollection(ArrayList::new));
//
//        newProcesses.add(proc1);
//
//        return newProcesses;
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
    private static AST.Process parStatementProcess(TLAExpr set, AST.Clause cl) {
        String processActionName = fresh("proc");
        Vector<AST.VarDecl> decls = new Vector<>();
        Vector<AST> body = new Vector<>();
        // TODO rename variables?
        if (cl.unlabOr != null) {
            body.addAll(cl.unlabOr);
        } else {
            body.addAll(cl.labOr);
        }
        return createProcess(processActionName, false, set, body, decls);
    }

    private static AST.Process allStatementProcess(String ig, TLAExpr ps) {

//    process (q \in qs)
//    variables auxps = ps;
//    {
//        while (auxps /= {}) {
//            with (pp \in { pr \in ps : pc[pr] = "pa" }) {
//                out := out \ union {<<pp, self>>};
//                auxps := auxps \ {pp};
//            }
//        }
//    }
        String p = fresh("proc");
        String auxps = fresh("ps");

        Vector<AST.VarDecl> decls = new Vector<>();
        {
            AST.VarDecl varDecl = new AST.VarDecl();
            varDecl.var = auxps;
            varDecl.isEq = true;
            varDecl.val = ps;
            decls.add(varDecl);
        }
        Vector<AST> body = new Vector<>();
        AST.With with = new AST.With();
        with.setOrigin(ps.getOrigin());
        String pp = fresh("pp");
        String pr = fresh("pr");
        String paLabel = fresh("pa"); // TODO
        with.exp = tlaExpr("%s \\in { %s \\in %s : pc[%s] = \"%s\"}", pp, pr, ps, pr, paLabel);
        // TODO rename q->self, p->pp
//        substituteForAll
        with.Do = new Vector<AST>();
        AST.Assign assign1 = new AST.Assign();
        assign1.setOrigin(ps.getOrigin());
        assign1.ass = new Vector<AST>();
        AST.SingleAssign a1 = new AST.SingleAssign();
        a1.setOrigin(ps.getOrigin());
        assign1.ass.add(a1);
        AST.Lhs lhs = new AST.Lhs();
        {
            lhs.setOrigin(ps.getOrigin());
            lhs.var = auxps;
//            lhs.sub = tlaExpr(""); // has to be initialized
            lhs.sub = PcalTranslate.MakeExpr(new Vector());
        }
        a1.lhs = lhs;
        a1.rhs = tlaExpr("%s \\ {{%s}}", auxps, pp);
        // TODO add the body here
        with.Do.add(assign1);
        AST.While loop = new AST.While();
        loop.test = tlaExpr("%s # {}", auxps);
        loop.unlabDo = new Vector<>();
        loop.unlabDo.add(with);
        loop.setOrigin(ps.getOrigin());
        body.add(loop);
        AST.Process proc = createProcess(p, false, ps, body, decls);
        return proc;
    }

    /**
     * Called for each statement of a process, which may generate more processes
     */
    private static WithProc<AST> expandParStatement(Map<String, Party> ownership,
                                                    Map<String, Party> partyDecls,
                                                    Party which,
                                                    AST stmt) {
        if (stmt instanceof AST.Par) {
            AST.Par par = (AST.Par) stmt;
            AST.When wait = new AST.When();
            wait.setOrigin(stmt.getOrigin());
            Vector<AST.Clause> clauses = par.clauses;
            List<AbstractMap.SimpleEntry<String, AST.Process>> threads = clauses.stream().map(c -> {
                String p = fresh(which.partyVar + "_par");
                String id = String.format("\"%s\"", p);
                TLAExpr set = tlaExpr("{%s}", id);
                return new AbstractMap.SimpleEntry<>(id, parStatementProcess(set, c));
            }).collect(Collectors.toList());

            String var = fresh("v");
            String s = threads.stream().map(AbstractMap.SimpleEntry::getKey).collect(Collectors.joining(", "));
            List<AST.Process> processes = threads.stream().map(AbstractMap.SimpleEntry::getValue).collect(Collectors.toList());
            wait.exp = tlaExpr("\\A %s \\in {%s} : pc[%s] = \"Done\"", var, s, var);
//           TODO recurse into proc?
            return new WithProc<>(wait, processes);
        } else {
            return new WithProc<>(stmt, List.of());
        }
    }

    private static WithProc<AST> expandAllStatement(Map<String, Party> ownership,
                                                    Map<String, Party> partyDecls,
                                                    AST stmt) {
        if (stmt instanceof AST.All) {
            AST.All all = (AST.All) stmt;
            AST.When wait = new AST.When();
            wait.setOrigin(stmt.getOrigin());
            wait.exp = tlaExpr("\\A %s \\in %s : pc[%s] = \"Done\"", all.var, all.exp, all.var);
            AST.Process proc = allStatementProcess(all.var, all.exp);
//           TODO recurse into proc
            return new WithProc<>(wait, List.of(proc));
//        } else if (stmt instanceof AST.With) {
//            return new WithProc<>(stmt, List.of());
        } else {
            return new WithProc<>(stmt, List.of());
        }
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

    private static Map<Party, AST.Process> project(Vector<AST.VarDecl> globals,
                                                   Map<String, Party> ownership,
                                                   Map<String, Party> partyDecls,
                                                   Map<String, AST.Cancel> cancellations, Vector<AST> stmts) {
        return partyDecls.entrySet().stream().map(e -> {
            Party party = e.getValue();
            Vector<AST> stmts1 = stmts.stream()
                    .map(s -> project(globals, ownership, cancellations, party, s))
                    .collect(Collectors.toCollection(Vector::new));
            AST.Process process = createProcess(party.partyVar, party.equalOrIn, party.partySet,
                    stmts1, new Vector(party.localVars));
            return new AbstractMap.SimpleEntry<>(party, process);
        }).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
    }

    /**
     * Main projection function, splitting a statement into its local equivalent for the given party,
     * with ownership as context
     */
    private static AST project(Vector<AST.VarDecl> globals,
                               Map<String, Party> ownership,
                               Map<String, AST.Cancel> cancellations,
                               Party party,
                               AST stmt) {
        // System.out.printf("project(%s, %s)\n", party.partyVar, stmt.getClass().getSimpleName());
        if (stmt instanceof AST.All) {
            AST.All e = (AST.All) stmt;
            AST.All e1 = new AST.All();
            e1.var = e.var;
            e1.isEq = e.isEq;
            e1.exp = e.exp;
            e1.Do = projectAll(globals, ownership, cancellations, e.Do, party);
            copyInto(e1, e);
            return e1;
//        } else if (stmt instanceof AST.Either) {
//            AST.Either e = (AST.Either) stmt;
//            AST.Either e1 = new AST.Either();
//            e1.ors = projectAll(ownership, party, e.ors);
//            return e1;
        } else if (stmt instanceof AST.LabelEither) {
            AST.LabelEither e = (AST.LabelEither) stmt;
            AST.LabelEither e1 = new AST.LabelEither();
            e1.clauses = projectAll(globals, ownership, cancellations, e.clauses, party);
            copyInto(e1, e);
            return e1;
        } else if (stmt instanceof AST.Par) {
            AST.Par e = (AST.Par) stmt;
            AST.Par e1 = new AST.Par();
            e1.clauses = projectAll(globals, ownership, cancellations, e.clauses, party);
            copyInto(e1, e);
            return e1;
        } else if (stmt instanceof AST.Task) {
            boolean thisParty = cancellations.get(((AST.Task) stmt).label).who.equals(party.partyVar);
            if (thisParty) {
                AST.Task e = (AST.Task) stmt;
                AST.Task e1 = new AST.Task();
                e1.label = e.label;
                e1.Do = projectAll(globals, ownership, cancellations, e.Do, party);
                copyInto(e1, e);
                return e1;
            } else {
                AST.Skip e2 = new AST.Skip();
                e2.setOrigin(stmt.getOrigin());
                return e2;
            }
//        } else if (stmt instanceof AST.With) {
             // TODO
        } else if (stmt instanceof AST.LabelIf) {
            AST.LabelIf e = (AST.LabelIf) stmt;
            AST.LabelIf e1 = new AST.LabelIf();
            // TODO check if test expressions all reside on same party
            e1.test = e.test;
            e1.unlabElse = projectAll(globals, ownership, cancellations, e.unlabElse, party);
            e1.unlabThen = projectAll(globals, ownership, cancellations, e.unlabThen, party);
            e1.labElse = projectAll(globals, ownership, cancellations, e.labElse, party);
            e1.labThen = projectAll(globals, ownership, cancellations, e.labThen, party);
            copyInto(e1, e);
            return e1;
        } else if (stmt instanceof AST.When) {
            AST.When e = (AST.When) stmt;
//            AST.When e1 = new AST.When();
//            copyInto(e1, e);
            // TODO check if test expressions all reside on same party
            return e;
        } else if (stmt instanceof AST.Clause) {
            AST.Clause e = (AST.Clause) stmt;
            AST.Clause e1 = new AST.Clause();
            e1.labOr = projectAll(globals, ownership, cancellations, e.labOr, party);
            e1.unlabOr = projectAll(globals, ownership, cancellations, e.unlabOr, party);
            copyInto(e1, e);
            return e1;
        } else if (stmt instanceof AST.Assign) {
            AST.Assign e = (AST.Assign) stmt;
            AST.Assign e1 = new AST.Assign();
            e1.ass = new Vector<>(((Vector<AST>) projectAll(globals, ownership, cancellations, e.ass, party)).stream()
                    // projection may create skips here; in that case drop those nodes
                    .filter(sa -> sa instanceof AST.SingleAssign)
                    .collect(Collectors.toList()));
            if (e1.ass.isEmpty()) {
                AST.Skip e2 = new AST.Skip();
                e2.setOrigin(e.getOrigin());
                return e2;
            }
            copyInto(e1, e);
            return e1;
        } else if (stmt instanceof AST.SingleAssign) {
            AST.SingleAssign e = (AST.SingleAssign) stmt;
            AST.Lhs lhs = e.lhs;

            // TODO check the rhs uses only expressions available on this party

            // try locals first
            Optional<AST.VarDecl> first = party.localVars.stream().filter(v -> v.var.equals(lhs.var)).findFirst();
            if (first.isPresent()) {
                return e;
            }

            // try globals
            Optional<AST.VarDecl> global = globals.stream().filter(v -> v.var.equals(lhs.var)).findFirst();
            if (global.isPresent()) {
                return e;
            }

            // this assignment must not involve this party
            AST.Skip e1 = new AST.Skip();
            // AST.Assert e1 = new AST.Assert();
            // e1.exp = tlaExpr("TRUE");
            copyInto(e1, e);
            return e1;
        } else if (stmt instanceof AST.Cancel) {
            AST.Cancel e = (AST.Cancel) stmt;
            AST e1;
            if (party.partyVar.equals(e.who)) {
                AST.Cancel e2 = new AST.Cancel();
                e2.to = e.to;
                e2.who = null; // deliberate, for now
                e1 = e2;
            } else {
                e1 = new AST.Skip();
            }
            copyInto(e1, e);
            return e1;
        } else if (stmt instanceof AST.MacroCall && ((AST.MacroCall) stmt).name.equals("Send")) {
            String sender = ithMacroArgAsVar((AST.MacroCall) stmt, 0);
            String receiver = ithMacroArgAsVar((AST.MacroCall) stmt, 1);
            boolean isSend = ownership.get(sender).partyVar.equals(party.partyVar);
            boolean isRecv = ownership.get(receiver).partyVar.equals(party.partyVar);
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
                return send;
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
                return recv;
            }
            // TODO self-send
            return null;
        } else {
            fail("unimplemented project(Party, AST) " + stmt);
            return null;
        }
    }

    private static Vector<AST> transformCancellations(Vector<AST> stmts) {
        return stmts.stream()
                .map(PlusCalExtensions::transformCancellations)
                .collect(Collectors.toCollection(Vector::new));
    }

    private static AST transformCancellations(AST stmt) {
        if (stmt instanceof AST.All) {
            AST.All e = (AST.All) stmt;
            AST.All e1 = new AST.All();
            e1.var = e.var;
            e1.isEq = e.isEq;
            e1.exp = e.exp;
            e1.Do = transformCancellations(e.Do);
            copyInto(e1, e);
            return e1;
        } else if (stmt instanceof AST.LabelEither) {
            AST.LabelEither e = (AST.LabelEither) stmt;
            AST.LabelEither e1 = new AST.LabelEither();
            e1.clauses = transformCancellations(e.clauses);
            copyInto(e1, e);
            return e1;
        } else if (stmt instanceof AST.Par) {
            AST.Par e = (AST.Par) stmt;
            AST.Par e1 = new AST.Par();
            e1.clauses = transformCancellations(e.clauses);
            copyInto(e1, e);
            return e1;
        } else if (stmt instanceof AST.LabelIf) {
            AST.LabelIf e = (AST.LabelIf) stmt;
            AST.LabelIf e1 = new AST.LabelIf();
            e1.test = e.test;
            e1.unlabElse = transformCancellations(e.unlabElse);
            e1.unlabThen = transformCancellations(e.unlabThen);
            e1.labElse = transformCancellations(e.labElse);
            e1.labThen = transformCancellations(e.labThen);
            copyInto(e1, e);
            return e1;
        } else if (stmt instanceof AST.When) {
            return stmt;
        } else if (stmt instanceof AST.With) {
            AST.With e = (AST.With) stmt;
            AST.With e1 = new AST.With();
            e1.var = e.var;
            e1.Do = transformCancellations(e.Do);
            copyInto(e1, e);
            return e1;
        } else if (stmt instanceof AST.Task) {
            AST.Task e = (AST.Task) stmt;
            AST.Task e1 = new AST.Task();
            e1.label = e.label;
            e1.Do = transformCancellations(e.Do);
            copyInto(e1, e);
            return e1;
        } else if (stmt instanceof AST.Clause) {
            AST.Clause e = (AST.Clause) stmt;
            AST.Clause e1 = new AST.Clause();
            e1.labOr = transformCancellations(e.labOr);
            e1.unlabOr = transformCancellations(e.unlabOr);
            copyInto(e1, e);
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
                String lbl = ((AST.Cancel) stmt).to;
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
            fail("unimplemented project(Party, AST) " + stmt);
            return null;
        }
    }

    public static AST.When convertTask(AST.Task task) {
        AST.When when = new AST.When();
        when.exp = tlaExpr("~ cancelled_%s", task.label);
        when.setOrigin(task.getOrigin());
        return when;
    }

    /**
     * For recursive calls
     */
    private static Vector<AST> projectAll(Vector<AST.VarDecl> globals, Map<String, Party> ownership, Map<String, AST.Cancel> cancellations, Vector<AST> all, Party party) {
        return all.stream()
                .map(s -> project(globals, ownership, cancellations, party, s))
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
