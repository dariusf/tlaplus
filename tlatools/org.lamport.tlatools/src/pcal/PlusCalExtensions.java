package pcal;

import pcal.exception.ParseAlgorithmException;
import pcal.exception.TokenizerException;

import java.util.*;
import java.util.stream.Collectors;

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


    public static List<AST.Process> GetChoreography() throws ParseAlgorithmException {
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

        // Translate into regular PlusCal
        Map<String, Party> quantified = computeOwnership(partyDecls, stmts);
        ownership.putAll(quantified);
        var res = project(ownership, partyDecls, stmts);

        var res1 = res.entrySet().stream()
                .flatMap(p -> expandAllStatement(ownership, partyDecls, p.getValue()).stream().map(pr -> new AbstractMap.SimpleEntry<>(p.getKey(), pr)))
                .flatMap(p -> expandParStatement(ownership, partyDecls, p.getKey(), p.getValue()).stream().map(pr -> new AbstractMap.SimpleEntry<>(p.getKey(), pr)))
                .map(Map.Entry::getValue)
                .collect(Collectors.toList());

        return res1;
    }

    /**
     * So when transforming a process recursively, anything nested inside can elaborate into more processes
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
     * Recurse into a process, expanding occurrences of par statements, which may generate more processes
     */
    private static List<AST.Process> expandParStatement(Map<String, Party> ownership,
                                                        Map<String, Party> partyDecls,
                                                        Party which,
                                                        AST.Process proc) {
        // TODO this is the same as expandAllStatement except for the function passed to map here
        List<WithProc<AST>> res = ((Vector<AST>) proc.body).stream()
                .map(s -> expandParStatement(ownership, partyDecls, which, s))
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
        List<WithProc<AST>> res = ((Vector<AST>) proc.body).stream()
                .map(s -> expandAllStatement(ownership, partyDecls, s))
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
            lhs.sub = tlaExpr(""); // has to be initialized
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
            var threads = clauses.stream().map(c -> {
                String p = fresh(which.partyVar + "_par");
                var id = String.format("\"%s\"", p);
                var set = tlaExpr("{%s}", id);
                return new AbstractMap.SimpleEntry<>(id, parStatementProcess(set, c));
            }).collect(Collectors.toList());

            var var = fresh("v");
            var s = threads.stream().map(AbstractMap.SimpleEntry::getKey).collect(Collectors.joining(", "));
            var processes = threads.stream().map(AbstractMap.SimpleEntry::getValue).collect(Collectors.toList());
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

    private static Map<Party, AST.Process> project(Map<String, Party> ownership,
                                                   Map<String, Party> partyDecls,
                                                   Vector<AST> stmts) {
        return partyDecls.entrySet().stream().map(e -> {
            Party party = e.getValue();
            Vector<AST> stmts1 = new Vector<>(stmts.stream()
                    .map(s -> project(ownership, party, s))
                    .collect(Collectors.toList()));
            AST.Process process = createProcess(party.partyVar, party.equalOrIn, party.partySet, stmts1, new Vector(party.localVars));
            return new AbstractMap.SimpleEntry<>(party, process);
        }).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
    }

    /**
     * Main projection function, splitting a statement into its local equivalent for the given party,
     * with ownership as context
     */
    private static AST project(Map<String, Party> ownership, Party party, AST stmt) {
        if (stmt instanceof AST.All) {
            AST.All e = (AST.All) stmt;
            AST.All e1 = new AST.All();
            e1.var = e.var;
            e1.isEq = e.isEq;
            e1.exp = e.exp;
            e1.Do = projectAll(ownership, party, e.Do);
            e1.setOrigin(e.getOrigin());
            return e1;
//        } else if (stmt instanceof AST.Either) {
//            AST.Either e = (AST.Either) stmt;
//            AST.Either e1 = new AST.Either();
//            e1.ors = projectAll(ownership, party, e.ors);
//            return e1;
        } else if (stmt instanceof AST.LabelEither) {
            AST.LabelEither e = (AST.LabelEither) stmt;
            AST.LabelEither e1 = new AST.LabelEither();
            e1.clauses = projectAll(ownership, party, e.clauses);
            e1.setOrigin(e.getOrigin());
            return e1;
        } else if (stmt instanceof AST.Par) {
            AST.Par e = (AST.Par) stmt;
            AST.Par e1 = new AST.Par();
            e1.clauses = projectAll(ownership, party, e.clauses);
            e1.setOrigin(e.getOrigin());
            return e1;
        } else if (stmt instanceof AST.LabelIf) {
            AST.LabelIf e = (AST.LabelIf) stmt;
            AST.LabelIf e1 = new AST.LabelIf();
            // TODO check if test expressions all reside on same party
            e1.test = e.test;
            e1.unlabElse = projectAll(ownership, party, e.unlabElse);
            e1.unlabThen = projectAll(ownership, party, e.unlabThen);
            e1.labElse = projectAll(ownership, party, e.labElse);
            e1.labThen = projectAll(ownership, party, e.labThen);
            e1.setOrigin(e.getOrigin());
            return e1;
        } else if (stmt instanceof AST.When) {
            AST.When e = (AST.When) stmt;
//            AST.When e1 = new AST.When();
//            e1.setOrigin(e.getOrigin());
            // TODO check if test expressions all reside on same party
            return e;
        } else if (stmt instanceof AST.Clause) {
            AST.Clause e = (AST.Clause) stmt;
            AST.Clause e1 = new AST.Clause();
            e1.labOr = projectAll(ownership, party, e.labOr);
            e1.unlabOr = projectAll(ownership, party, e.unlabOr);
            e1.setOrigin(e.getOrigin());
            return e1;
        } else if (stmt instanceof AST.Assign) {
            AST.Assign e = (AST.Assign) stmt;
            AST.Assign e1 = new AST.Assign();
            e1.ass = new Vector<>(((Vector<AST>) projectAll(ownership, party, e.ass)).stream()
                    // projection may create skips here; in that case drop those nodes
                    .filter(sa -> sa instanceof AST.SingleAssign)
                    .collect(Collectors.toList()));
            if (e1.ass.isEmpty()) {
                AST.Skip e2 = new AST.Skip();
                e2.setOrigin(e.getOrigin());
                return e2;
            }
            e1.setOrigin(e.getOrigin());
            return e1;
        } else if (stmt instanceof AST.SingleAssign) {
            AST.SingleAssign e = (AST.SingleAssign) stmt;
            AST.Lhs lhs = e.lhs;
            // TODO check the rhs uses only expressions available on this party
            Optional<AST.VarDecl> first = party.localVars.stream().filter(v -> v.var.equals(lhs.var)).findFirst();
            if (first.isPresent()) {
                return e;
            } else {
                AST.Skip e1 = new AST.Skip();
                // AST.Assert e1 = new AST.Assert();
                // e1.exp = tlaExpr("TRUE");
                e1.setOrigin(e.getOrigin());
                return e1;
            }
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

    /**
     * For recursive calls
     */
    private static Vector<AST> projectAll(Map<String, Party> ownership, Party party, Vector<AST> all) {
        return new Vector<>(all.stream()
                .map(s -> project(ownership, party, s))
                .collect(Collectors.toList()));
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
