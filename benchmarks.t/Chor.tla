--------------------- MODULE Chor ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, coord

(* --algorithm Chor {
  variables
    participants = {p1, p2};
    out = {};
    messages = {};

  macro Send(from, to, type) {
    messages := messages \union {[To |-> to, From |-> from, Type |-> type]};
  }

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (P \in participants),
    (C = coord)
      variables
        aborted = {},
        committed = {},
        has_aborted = FALSE;
  {
    all (p \in participants) {
      Send(coord, p, "prepare");
      out := out \union {<<p, coord>>};
    }
  }
}

*)

==================================================================
