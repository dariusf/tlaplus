--------------------- MODULE Par ----------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS p1, p2, coord

(* --algorithm Chor {
  \* variables x = 1;

  macro Receive(from, to, type) {
    await [To |-> to, From |-> from, Type |-> type] \in messages;
  }

  choreography
    (P \in participants),
    (C = coord)
      variables x = 1;
  {
    par {
      x := x + 1;
    } and {
      x := x + 2;
    }
  }
}

*)

==================================================================
