package tlc2.mbtc;

import tla2sany.semantic.*;
import tlc2.synth.Visitor;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.ToolGlobals;
import tlc2.tool.impl.FastTool;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import util.UniqueString;

import java.util.*;
import java.util.stream.Collectors;

import static tlc2.tool.ToolGlobals.*;

public class FindActionVisitor extends Visitor<FindActionVisitor.R> {

    public static class Act {
        OpApplNode action;
        // TODO contextual precondition

        /*
Next ==
  \/
    LET msgs == MsgsIn(inbox) IN
    \E i \in 1..Len(msgs) : ReceiveMsg(msgs[i])
  \/ ...

ReceiveMsg(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = "RequestVoteRequest"
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = "RequestVoteResponse"
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = "AppendEntriesRequest"
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = "AppendEntriesResponse"
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)


the precondition of DropStaleResponse is:

/\ msgs = MsgsIn(inbox)
/\ \E i \in 1..Len(msgs)
/\ i = m.mdest
/\ j = m.msource
/\
  \/ m.mtype = "RequestVoteResponse"
  \/ m.mtype = "AppendEntriesResponse"

on top of everything inside

        */
    }
    public static class R {
        Map<String, Act> actions = new HashMap<>();
    }

    private final FastTool tool;
    private final Stack<String> names = new Stack<>();

    public FindActionVisitor(FastTool tool) {
        this.tool = tool;
    }

    @Override
    public R visit(OpApplNode node) {
        UniqueString opName = node.getOperator().getName();
        int opCode = BuiltInOPs.getOpCode(opName);
        if (opCode == OPCODE_be) {
            // TODO store pre
            return node.getArgs()[0].accept(this);
        } else if (opCode == OPCODE_cl) {

            // assume an action will have a top-level conjunction
            boolean isAction = Arrays.stream(node.getArgs()).anyMatch(a -> a instanceof OpApplNode && ((OpApplNode) a).getOperator().getName().equals("LogAction"));
            if (isAction) {
                R res = new R();
                Act a = new Act();
                a.action = node;
                String name = names.peek();
                res.actions.put(name, a);
                return res;
            }
            // TODO add to pre
            List<R> args = Arrays.stream(node.getArgs())
                    .map(n -> n.accept(this))
                    .collect(Collectors.toList());
            R res = new R();
            args.forEach(r -> r.actions.forEach((k, v) -> res.actions.merge(k, v, (v1, v2) -> v1)));
            return res;
        } else if (opCode == OPCODE_dl) {
            // TODO add disjuncts to pre
            List<R> args = Arrays.stream(node.getArgs())
                    .map(n -> n.accept(this))
                    .collect(Collectors.toList());
            R res = new R();
            args.forEach(r -> r.actions.forEach((k, v) -> res.actions.merge(k, v, (v1, v2) -> v1)));
            return res;
        } else if (opCode == 0) {
            Object def = tool.getSpecProcessor().getDefns().get(opName.toString());
            if (def instanceof OpDefNode) {
                // we're dealing with a user-defined function. recurse on its body
                names.push(opName.toString());
                R z = ((OpDefNode) def).getBody().accept(this);
                names.pop();
                return z;
            }
//            return new R();
            // prob return nothing for things implemented as java methods
            throw new RuntimeException("unimplemented");
        } else {
            // we got some other prop, e.g.
            // /\ prop <- this
            // /\ Action(...)
            // TODO add to precondition
            return new R();
        }
    }

    @Override
    public R visit(LetInNode node) {
        // TODO store pre
        return node.getBody().accept(this);
    }

    @Override
    public R visit(NumeralNode node) {
        return new R();
    }

    @Override
    public R visit(StringNode node) {
        return new R();
    }

    @Override
    public R visit(OpArgNode node) {
        return new R();
    }

    @Override
    public R visit(ExprOrOpArgNode node) {
        return new R();
    }

    @Override
    public R visit(IntValue intValue) {
        return new R();
    }

    @Override
    public R visit(RecordValue recordValue) {
        return new R();
    }

    @Override
    public R visit(StringValue stringValue) {
        return new R();
    }
}
