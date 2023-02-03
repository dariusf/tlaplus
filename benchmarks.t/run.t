
  $ source ../build.sh; tla2tools=../tlatools/org.lamport.tlatools/dist/tla2tools.jar

  $ pluscal -label Par.tla | make_det
  pcal.trans Version 1.11 of 31 December 2020
  Labels added.
  Parsing completed.
  Translation completed.
  New file Par.tla written.
  New file Par.cfg written.

  $ cat Par.tla
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
  \* BEGIN TRANSLATION (chksum(pcal) = "14a449db" /\ chksum(tla) = "916b23d6")
  VARIABLES pc, x
  
  vars == << pc, x >>
  
  ProcSet == ({"P_par_0"}) \cup ({"P_par_2"}) \cup (participants) \cup ({"C_par_5"}) \cup ({"C_par_7"}) \cup {coord}
  
  Init == (* Process C *)
          /\ x = 1
          /\ pc = [self \in ProcSet |-> CASE self \in {"P_par_0"} -> "Lbl_1"
                                          [] self \in {"P_par_2"} -> "Lbl_2"
                                          [] self \in participants -> "Lbl_3"
                                          [] self \in {"C_par_5"} -> "Lbl_4"
                                          [] self \in {"C_par_7"} -> "Lbl_5"
                                          [] self = coord -> "Lbl_6"]
  
  Lbl_1(self) == /\ pc[self] = "Lbl_1"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ x' = x
  
  proc_1(self) == Lbl_1(self)
  
  Lbl_2(self) == /\ pc[self] = "Lbl_2"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ x' = x
  
  proc_3(self) == Lbl_2(self)
  
  Lbl_3(self) == /\ pc[self] = "Lbl_3"
                 /\ \A v_4 \in {"P_par_0", "P_par_2"} : pc[v_4] = "Done"
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ x' = x
  
  P(self) == Lbl_3(self)
  
  Lbl_4(self) == /\ pc[self] = "Lbl_4"
                 /\ x' = x + 1
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
  
  proc_6(self) == Lbl_4(self)
  
  Lbl_5(self) == /\ pc[self] = "Lbl_5"
                 /\ x' = x + 2
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
  
  proc_8(self) == Lbl_5(self)
  
  Lbl_6 == /\ pc[coord] = "Lbl_6"
           /\ \A v_9 \in {"C_par_5", "C_par_7"} : pc[v_9] = "Done"
           /\ pc' = [pc EXCEPT ![coord] = "Done"]
           /\ x' = x
  
  C == Lbl_6
  
  (* Allow infinite stuttering to prevent deadlock on termination. *)
  Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
                 /\ UNCHANGED vars
  
  Next == C
             \/ (\E self \in {"P_par_0"}: proc_1(self))
             \/ (\E self \in {"P_par_2"}: proc_3(self))
             \/ (\E self \in participants: P(self))
             \/ (\E self \in {"C_par_5"}: proc_6(self))
             \/ (\E self \in {"C_par_7"}: proc_8(self))
             \/ Terminating
  
  Spec == Init /\ [][Next]_vars
  
  Termination == <>(\A self \in ProcSet: pc[self] = "Done")
  
  \* END TRANSLATION 
  
  ==================================================================

  $ pluscal -label Chor.tla | grep Exception
  Exception in thread "main" java.lang.Error: unimplemented project(Party, AST) [type    |-> "while", 

  $ cat Chor.tla
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

  $ source test.sh

  $ monitor_check Counter
  compile ok
  package monitoring
  
  import (
  	"fmt"
  	"path"
  	"reflect"
  	"runtime"
  	"strings"
  )
  
  // panic instead of returning error
  var crash = true
  
  func thisFile() string {
  	_, file, _, ok := runtime.Caller(1)
  	if ok {
  		return file
  	}
  	panic("could not get this file")
  }
  
  func getFileLine() (string, int) {
  	for i := 1; i < 10; i++ {
  		_, f, l, _ := runtime.Caller(i)
  		if !strings.Contains(f, thisFile()) {
  			return f, l
  		}
  	}
  	panic("could not get file and line")
  }
  
  type State struct {
  	x any
  }
  
  type EventType int
  
  const (
  	Initial = iota // special
  	A
  	Constr
  	Inv
  )
  
  func (e EventType) String() string {
  	switch e {
  	case Initial:
  		return "Initial"
  	case A:
  		return "A"
  	case Constr:
  		return "Constr"
  	case Inv:
  		return "Inv"
  	default:
  		panic(fmt.Sprintf("invalid %d", e))
  	}
  }
  
  type Event struct {
  	typ    EventType
  	params []any
  	state  State
  	file   string
  	line   int
  }
  
  func printParams(ps []any) string {
  	res := []string{}
  	for _, v := range ps {
  		res = append(res, fmt.Sprintf("%+v", v))
  	}
  	return strings.Join(res, ", ")
  }
  
  func (e Event) String() string {
  	return fmt.Sprintf("%s(%s);%s:%d;%+v",
  		e.typ, printParams(e.params), path.Base(e.file), e.line, e.state)
  }
  
  /*
  type Constants struct {
      %s
  }
  */
  
  type Monitor struct {
  	// the goal of extra is just to remove maintaining our own aux state,
  	// which is annoying and error-prone as it may have to be passed across several functions
  	extra  []Event
  	events []Event
  	//constants Constants
  }
  
  func New( /* constants Constants */ ) Monitor {
  	return Monitor{
  		extra:  []Event{},
  		events: []Event{},
  		//constants: constants,
  	}
  }
  
  // TODO check initial
  
  func (m *Monitor) CheckTrace() error {
  	var prev Event
  	for i, this := range m.events {
  		if i == 0 {
  			prev = this
  		}
  		switch this.typ {
  		case Initial:
  			if err := m.CheckInitial(i, Event{}, this); err != nil {
  				return err
  			}
  		case A:
  			if err := m.CheckA(i, prev, this); err != nil {
  				return err
  			}
  		case Constr:
  			if err := m.CheckConstr(i, prev, this); err != nil {
  				return err
  			}
  		case Inv:
  			if err := m.CheckInv(i, prev, this); err != nil {
  				return err
  			}
  		}
  		prev = this
  	}
  	return nil
  }
  
  func (m *Monitor) ShowTrace() {
  	for i, v := range m.events {
  		fmt.Printf("%d;%+v\n", i, v)
  	}
  }
  
  func fail(format string, a ...any) error {
  	if crash {
  		panic(fmt.Sprintf(format, a...))
  	}
  	return fmt.Errorf(format, a...)
  }
  
  func (m *Monitor) CheckInitial(trace_i int, prev Event, this Event) error {
  
  	if !(!reflect.DeepEqual(this.state.x, 1)) {
  		return fail("initial state precondition failed at %d; x = 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckA(trace_i int, prev Event, this Event) error {
  
  	if !(reflect.DeepEqual(this.state.x, (prev.state.x.(int) + 1))) {
  		return fail("postcondition failed at %d; '(x) = x + 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckConstr(trace_i int, prev Event, this Event) error {
  
  	if !(prev.state.x.(int) < 2) {
  		return fail("precondition failed at %d; x < 2 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckInv(trace_i int, prev Event, this Event) error {
  
  	if !(prev.state.x.(int) < 3) {
  		return fail("precondition failed at %d; x < 3 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  /*
  func (m *Monitor) CheckInc(i int, prev Event, this Event) error {
  
  	if prev.state.x.(int) <= 0 {
  		return fail("precondition failed at %d; expected x <= 0 but got %s (prev: %+v, this: %+v)", i, prev.state.x, prev, this)
  	}
  	// check that new values are allowed
  	if this.state.x != prev.state.x.(int)+1 { // for each var
  		return fail("postcondition violated for x at %d; should be %+v but got %+v (prev: %+v, this: %+v)", i,
  			prev.state.x.(int)+1, this.state.x, prev, this)
  	}
  
  	// check unchanged
  	if this.state.x != prev.state.x { // for each var
  		return fail("unchanged violated for x at %d; expected x to remain as %+v but it is %+v (prev: %+v, this: %+v)", i, prev.state.x, this.state.x, prev, this)
  	}
  
  	return nil
  }
  */
  
  // this state value can have nil fields
  func (m *Monitor) CaptureVariable(v State, typ EventType, args ...any) error {
  
  	e := Event{
  		typ:    typ,
  		params: args,
  		state:  v,
  		// no need to capture file and line here
  	}
  	m.extra = append(m.extra, e)
  	return nil
  }
  
  func (m *Monitor) CaptureState(c State, typ EventType, args ...any) error {
  
  	// override current values with extras
  	// all have to pertain to this action
  	for _, v := range m.extra {
  		// sanity checks
  		if v.typ != typ {
  			return fmt.Errorf("type did not match")
  		}
  		for i, p := range v.params {
  			if p != args[i] {
  				return fmt.Errorf("arg %d did not match", i)
  			}
  		}
  		// there is no null in TLA+, and also all the struct fields are any, which are reference types
  
  		// for each variable in state
  		if v.state.x != nil {
  			c.x = v.state.x
  		}
  	}
  
  	// reset
  	m.extra = []Event{}
  
  	// record event
  	file, line := getFileLine()
  	e := Event{
  		typ:    typ,
  		params: args,
  		state:  c,
  		file:   file,
  		line:   line,
  	}
  
  	m.events = append(m.events, e)
  
  	return nil
  }

  $ monitor_check Stress
  compile ok
  package monitoring
  
  import (
  	"fmt"
  	"path"
  	"reflect"
  	"runtime"
  	"strings"
  )
  
  // panic instead of returning error
  var crash = true
  
  func thisFile() string {
  	_, file, _, ok := runtime.Caller(1)
  	if ok {
  		return file
  	}
  	panic("could not get this file")
  }
  
  func getFileLine() (string, int) {
  	for i := 1; i < 10; i++ {
  		_, f, l, _ := runtime.Caller(i)
  		if !strings.Contains(f, thisFile()) {
  			return f, l
  		}
  	}
  	panic("could not get file and line")
  }
  
  type State struct {
  	x any
  }
  
  type EventType int
  
  const (
  	Initial = iota // special
  	A
  	A1
  	B
  	C
  	D
  	E
  	F
  	G
  	H
  	H1
  	H2
  	H3
  	I1
  )
  
  func (e EventType) String() string {
  	switch e {
  	case Initial:
  		return "Initial"
  	case A:
  		return "A"
  	case A1:
  		return "A1"
  	case B:
  		return "B"
  	case C:
  		return "C"
  	case D:
  		return "D"
  	case E:
  		return "E"
  	case F:
  		return "F"
  	case G:
  		return "G"
  	case H:
  		return "H"
  	case H1:
  		return "H1"
  	case H2:
  		return "H2"
  	case H3:
  		return "H3"
  	case I1:
  		return "I1"
  	default:
  		panic(fmt.Sprintf("invalid %d", e))
  	}
  }
  
  type Event struct {
  	typ    EventType
  	params []any
  	state  State
  	file   string
  	line   int
  }
  
  func printParams(ps []any) string {
  	res := []string{}
  	for _, v := range ps {
  		res = append(res, fmt.Sprintf("%+v", v))
  	}
  	return strings.Join(res, ", ")
  }
  
  func (e Event) String() string {
  	return fmt.Sprintf("%s(%s);%s:%d;%+v",
  		e.typ, printParams(e.params), path.Base(e.file), e.line, e.state)
  }
  
  /*
  type Constants struct {
      %s
  }
  */
  
  type Monitor struct {
  	// the goal of extra is just to remove maintaining our own aux state,
  	// which is annoying and error-prone as it may have to be passed across several functions
  	extra  []Event
  	events []Event
  	//constants Constants
  }
  
  func New( /* constants Constants */ ) Monitor {
  	return Monitor{
  		extra:  []Event{},
  		events: []Event{},
  		//constants: constants,
  	}
  }
  
  // TODO check initial
  
  func (m *Monitor) CheckTrace() error {
  	var prev Event
  	for i, this := range m.events {
  		if i == 0 {
  			prev = this
  		}
  		switch this.typ {
  		case Initial:
  			if err := m.CheckInitial(i, Event{}, this); err != nil {
  				return err
  			}
  		case A:
  			if err := m.CheckA(i, prev, this); err != nil {
  				return err
  			}
  		case A1:
  			if err := m.CheckA1(i, prev, this); err != nil {
  				return err
  			}
  		case B:
  			if err := m.CheckB(i, prev, this); err != nil {
  				return err
  			}
  		case C:
  			if err := m.CheckC(i, prev, this); err != nil {
  				return err
  			}
  		case D:
  			if err := m.CheckD(i, prev, this); err != nil {
  				return err
  			}
  		case E:
  			if err := m.CheckE(i, prev, this); err != nil {
  				return err
  			}
  		case F:
  			if err := m.CheckF(this.params[0], i, prev, this); err != nil {
  				return err
  			}
  		case G:
  			if err := m.CheckG(i, prev, this); err != nil {
  				return err
  			}
  		case H:
  			if err := m.CheckH(i, prev, this); err != nil {
  				return err
  			}
  		case H1:
  			if err := m.CheckH1(i, prev, this); err != nil {
  				return err
  			}
  		case H2:
  			if err := m.CheckH2(i, prev, this); err != nil {
  				return err
  			}
  		case H3:
  			if err := m.CheckH3(i, prev, this); err != nil {
  				return err
  			}
  		case I1:
  			if err := m.CheckI1(i, prev, this); err != nil {
  				return err
  			}
  		}
  		prev = this
  	}
  	return nil
  }
  
  func (m *Monitor) ShowTrace() {
  	for i, v := range m.events {
  		fmt.Printf("%d;%+v\n", i, v)
  	}
  }
  
  func fail(format string, a ...any) error {
  	if crash {
  		panic(fmt.Sprintf(format, a...))
  	}
  	return fmt.Errorf(format, a...)
  }
  
  func (m *Monitor) CheckInitial(trace_i int, prev Event, this Event) error {
  
  	if !(!reflect.DeepEqual(this.state.x, 1)) {
  		return fail("initial state precondition failed at %d; x = 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckA(trace_i int, prev Event, this Event) error {
  
  	if !(prev.state.x.(int) < 0) {
  		return fail("precondition failed at %d; x < 0 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.x, (prev.state.x.(int) + 1))) {
  		return fail("postcondition failed at %d; '(x) = x + 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckA1(trace_i int, prev Event, this Event) error {
  
  	if !(prev.state.x.(int) < 0) {
  		return fail("precondition failed at %d; x < 0 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.x, (prev.state.x.(int)+1)) && (prev.state.x.(int) < 0)) {
  		return fail("precondition failed at %d; '(x) = x + 1 \\land x < 0 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckB(trace_i int, prev Event, this Event) error {
  
  	if !(reflect.DeepEqual(this.state.x, prev.state.x)) {
  		return fail("precondition failed at %d; UNCHANGED(x) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckC(trace_i int, prev Event, this Event) error {
  
  	if !(reflect.DeepEqual(prev.state.x, prev.state.x)) {
  		return fail("precondition failed at %d; Send(x) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckD(trace_i int, prev Event, this Event) error {
  
  	if !(reflect.DeepEqual(prev.state.x, 1) && reflect.DeepEqual(this.state.x, 2)) {
  
  		if !(!reflect.DeepEqual(prev.state.x, 1) && reflect.DeepEqual(this.state.x, 3)) {
  
  			if !(!reflect.DeepEqual(prev.state.x, 1) && reflect.DeepEqual(this.state.x, 3)) {
  				return fail("precondition failed at %d; ((x = 1 /\\ '(x) = 2) \\/ (x /= 1 /\\ '(x) = 3)) (prev: %+v, this: %+v)", trace_i, prev, this)
  			}
  		}
  
  	}
  
  	return nil
  }
  
  func (m *Monitor) CheckE(trace_i int, prev Event, this Event) error {
  
  	if !((reflect.DeepEqual(prev.state.x, 1) && reflect.DeepEqual(this.state.x, 2)) && (reflect.DeepEqual(prev.state.x, 2) || (reflect.DeepEqual(prev.state.x, 3) && reflect.DeepEqual(prev.state.x, 1)))) {
  
  		if !(!reflect.DeepEqual(prev.state.x, 1) && reflect.DeepEqual(this.state.x, 3)) {
  
  			if !(!reflect.DeepEqual(prev.state.x, 1) && reflect.DeepEqual(this.state.x, 3)) {
  				return fail("precondition failed at %d; ((x = 1 /\\ '(x) = 2) \\/ (x /= 1 /\\ '(x) = 3)) (prev: %+v, this: %+v)", trace_i, prev, this)
  			}
  		}
  
  	}
  
  	return nil
  }
  
  func (m *Monitor) CheckF(z any, trace_i int, prev Event, this Event) error {
  
  	if !(true) {
  		return fail("precondition failed at %d; TRUE (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckG(trace_i int, prev Event, this Event) error {
  
  	v0 := map[any]any{}
  	for v1, v2 := range map[string]any{"a": 1} {
  		v0[v1] = v2
  	}
  	v0["a"] = 2
  	if !(reflect.DeepEqual(v0["a"], 2)) {
  		return fail("precondition failed at %d; [[\"a\" |-> 1] EXCEPT ![\"a\"] = 2][\"a\"] = 2 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckH(trace_i int, prev Event, this Event) error {
  
  	v3 := true
  	for v4, _ := range map[any]bool{1: true, 2: true} {
  		v3 = v3 && reflect.DeepEqual(v4, 1)
  	}
  	if !(v3) {
  		return fail("precondition failed at %d; \\A r \\in {1, 2} : r = 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckH1(trace_i int, prev Event, this Event) error {
  
  	v5 := true
  	for v6, _ := range map[any]bool{1: true, 2: true} {
  		v7 := true
  		for v8, _ := range map[any]bool{3: true, 4: true} {
  			v7 = v7 && reflect.DeepEqual(v8, v6)
  		}
  		v5 = v5 && v7
  	}
  	if !(v5) {
  		return fail("precondition failed at %d; \\A s \\in {1, 2} : \\A r \\in {3, 4} : r = s (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckH2(trace_i int, prev Event, this Event) error {
  
  	v9 := map[any]any{}
  	for v10, _ := range map[any]bool{} {
  		v9[v10] = "a"
  	}
  
  	if !(reflect.DeepEqual(v9["a"], 1)) {
  		return fail("precondition failed at %d; [ r \\in RM |-> \"a\" ][\"a\"] = 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckH3(trace_i int, prev Event, this Event) error {
  
  	v12 := map[any]any{}
  	for v13, v14 := range map[any]bool{} {
  		v12[v13] = v14
  	}
  
  	if !(reflect.DeepEqual(v12["a"], 1)) {
  		return fail("precondition failed at %d; [ r \\in RM |-> r ][\"a\"] = 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  /* Action I cannot be translated because of: ToTrace(CounterExample) */
  
  /* Action a cannot be translated because of: a is not an OpApplNode but an NumeralNode */
  
  /* Action b cannot be translated because of: b is not an OpApplNode but an NumeralNode */
  
  /* Action c cannot be translated because of: c is not an OpApplNode but an NumeralNode */
  
  func (m *Monitor) CheckI1(trace_i int, prev Event, this Event) error {
  
  	a := 1
  	b := 1
  	c := 1
  	if !(reflect.DeepEqual(((a + b) + c), 1)) {
  		return fail("precondition failed at %d; a + b + c = 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  /*
  func (m *Monitor) CheckInc(i int, prev Event, this Event) error {
  
  	if prev.state.x.(int) <= 0 {
  		return fail("precondition failed at %d; expected x <= 0 but got %s (prev: %+v, this: %+v)", i, prev.state.x, prev, this)
  	}
  	// check that new values are allowed
  	if this.state.x != prev.state.x.(int)+1 { // for each var
  		return fail("postcondition violated for x at %d; should be %+v but got %+v (prev: %+v, this: %+v)", i,
  			prev.state.x.(int)+1, this.state.x, prev, this)
  	}
  
  	// check unchanged
  	if this.state.x != prev.state.x { // for each var
  		return fail("unchanged violated for x at %d; expected x to remain as %+v but it is %+v (prev: %+v, this: %+v)", i, prev.state.x, this.state.x, prev, this)
  	}
  
  	return nil
  }
  */
  
  // this state value can have nil fields
  func (m *Monitor) CaptureVariable(v State, typ EventType, args ...any) error {
  
  	e := Event{
  		typ:    typ,
  		params: args,
  		state:  v,
  		// no need to capture file and line here
  	}
  	m.extra = append(m.extra, e)
  	return nil
  }
  
  func (m *Monitor) CaptureState(c State, typ EventType, args ...any) error {
  
  	// override current values with extras
  	// all have to pertain to this action
  	for _, v := range m.extra {
  		// sanity checks
  		if v.typ != typ {
  			return fmt.Errorf("type did not match")
  		}
  		for i, p := range v.params {
  			if p != args[i] {
  				return fmt.Errorf("arg %d did not match", i)
  			}
  		}
  		// there is no null in TLA+, and also all the struct fields are any, which are reference types
  
  		// for each variable in state
  		if v.state.x != nil {
  			c.x = v.state.x
  		}
  	}
  
  	// reset
  	m.extra = []Event{}
  
  	// record event
  	file, line := getFileLine()
  	e := Event{
  		typ:    typ,
  		params: args,
  		state:  c,
  		file:   file,
  		line:   line,
  	}
  
  	m.events = append(m.events, e)
  
  	return nil
  }

  $ monitor_check Counter
  compile ok
  package monitoring
  
  import (
  	"fmt"
  	"path"
  	"reflect"
  	"runtime"
  	"strings"
  )
  
  // panic instead of returning error
  var crash = true
  
  func thisFile() string {
  	_, file, _, ok := runtime.Caller(1)
  	if ok {
  		return file
  	}
  	panic("could not get this file")
  }
  
  func getFileLine() (string, int) {
  	for i := 1; i < 10; i++ {
  		_, f, l, _ := runtime.Caller(i)
  		if !strings.Contains(f, thisFile()) {
  			return f, l
  		}
  	}
  	panic("could not get file and line")
  }
  
  type State struct {
  	x any
  }
  
  type EventType int
  
  const (
  	Initial = iota // special
  	A
  	Constr
  	Inv
  )
  
  func (e EventType) String() string {
  	switch e {
  	case Initial:
  		return "Initial"
  	case A:
  		return "A"
  	case Constr:
  		return "Constr"
  	case Inv:
  		return "Inv"
  	default:
  		panic(fmt.Sprintf("invalid %d", e))
  	}
  }
  
  type Event struct {
  	typ    EventType
  	params []any
  	state  State
  	file   string
  	line   int
  }
  
  func printParams(ps []any) string {
  	res := []string{}
  	for _, v := range ps {
  		res = append(res, fmt.Sprintf("%+v", v))
  	}
  	return strings.Join(res, ", ")
  }
  
  func (e Event) String() string {
  	return fmt.Sprintf("%s(%s);%s:%d;%+v",
  		e.typ, printParams(e.params), path.Base(e.file), e.line, e.state)
  }
  
  /*
  type Constants struct {
      %s
  }
  */
  
  type Monitor struct {
  	// the goal of extra is just to remove maintaining our own aux state,
  	// which is annoying and error-prone as it may have to be passed across several functions
  	extra  []Event
  	events []Event
  	//constants Constants
  }
  
  func New( /* constants Constants */ ) Monitor {
  	return Monitor{
  		extra:  []Event{},
  		events: []Event{},
  		//constants: constants,
  	}
  }
  
  // TODO check initial
  
  func (m *Monitor) CheckTrace() error {
  	var prev Event
  	for i, this := range m.events {
  		if i == 0 {
  			prev = this
  		}
  		switch this.typ {
  		case Initial:
  			if err := m.CheckInitial(i, Event{}, this); err != nil {
  				return err
  			}
  		case A:
  			if err := m.CheckA(i, prev, this); err != nil {
  				return err
  			}
  		case Constr:
  			if err := m.CheckConstr(i, prev, this); err != nil {
  				return err
  			}
  		case Inv:
  			if err := m.CheckInv(i, prev, this); err != nil {
  				return err
  			}
  		}
  		prev = this
  	}
  	return nil
  }
  
  func (m *Monitor) ShowTrace() {
  	for i, v := range m.events {
  		fmt.Printf("%d;%+v\n", i, v)
  	}
  }
  
  func fail(format string, a ...any) error {
  	if crash {
  		panic(fmt.Sprintf(format, a...))
  	}
  	return fmt.Errorf(format, a...)
  }
  
  func (m *Monitor) CheckInitial(trace_i int, prev Event, this Event) error {
  
  	if !(!reflect.DeepEqual(this.state.x, 1)) {
  		return fail("initial state precondition failed at %d; x = 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckA(trace_i int, prev Event, this Event) error {
  
  	if !(reflect.DeepEqual(this.state.x, (prev.state.x.(int) + 1))) {
  		return fail("postcondition failed at %d; '(x) = x + 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckConstr(trace_i int, prev Event, this Event) error {
  
  	if !(prev.state.x.(int) < 2) {
  		return fail("precondition failed at %d; x < 2 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckInv(trace_i int, prev Event, this Event) error {
  
  	if !(prev.state.x.(int) < 3) {
  		return fail("precondition failed at %d; x < 3 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  /*
  func (m *Monitor) CheckInc(i int, prev Event, this Event) error {
  
  	if prev.state.x.(int) <= 0 {
  		return fail("precondition failed at %d; expected x <= 0 but got %s (prev: %+v, this: %+v)", i, prev.state.x, prev, this)
  	}
  	// check that new values are allowed
  	if this.state.x != prev.state.x.(int)+1 { // for each var
  		return fail("postcondition violated for x at %d; should be %+v but got %+v (prev: %+v, this: %+v)", i,
  			prev.state.x.(int)+1, this.state.x, prev, this)
  	}
  
  	// check unchanged
  	if this.state.x != prev.state.x { // for each var
  		return fail("unchanged violated for x at %d; expected x to remain as %+v but it is %+v (prev: %+v, this: %+v)", i, prev.state.x, this.state.x, prev, this)
  	}
  
  	return nil
  }
  */
  
  // this state value can have nil fields
  func (m *Monitor) CaptureVariable(v State, typ EventType, args ...any) error {
  
  	e := Event{
  		typ:    typ,
  		params: args,
  		state:  v,
  		// no need to capture file and line here
  	}
  	m.extra = append(m.extra, e)
  	return nil
  }
  
  func (m *Monitor) CaptureState(c State, typ EventType, args ...any) error {
  
  	// override current values with extras
  	// all have to pertain to this action
  	for _, v := range m.extra {
  		// sanity checks
  		if v.typ != typ {
  			return fmt.Errorf("type did not match")
  		}
  		for i, p := range v.params {
  			if p != args[i] {
  				return fmt.Errorf("arg %d did not match", i)
  			}
  		}
  		// there is no null in TLA+, and also all the struct fields are any, which are reference types
  
  		// for each variable in state
  		if v.state.x != nil {
  			c.x = v.state.x
  		}
  	}
  
  	// reset
  	m.extra = []Event{}
  
  	// record event
  	file, line := getFileLine()
  	e := Event{
  		typ:    typ,
  		params: args,
  		state:  c,
  		file:   file,
  		line:   line,
  	}
  
  	m.events = append(m.events, e)
  
  	return nil
  }

  $ monitor_check TwoPhaseCommitFull
  compile ok
  package monitoring
  
  import (
  	"fmt"
  	"path"
  	"reflect"
  	"runtime"
  	"strings"
  )
  
  // panic instead of returning error
  var crash = true
  
  func thisFile() string {
  	_, file, _, ok := runtime.Caller(1)
  	if ok {
  		return file
  	}
  	panic("could not get this file")
  }
  
  func getFileLine() (string, int) {
  	for i := 1; i < 10; i++ {
  		_, f, l, _ := runtime.Caller(i)
  		if !strings.Contains(f, thisFile()) {
  			return f, l
  		}
  	}
  	panic("could not get file and line")
  }
  
  type State struct {
  	who             any
  	lastMsgReceived any
  	tmCommitted     any
  	lastMsgSent     any
  	tmPrepared      any
  	msgs            any
  	tmAborted       any
  	rmState         any
  }
  
  type EventType int
  
  const (
  	Initial = iota // special
  	CReceivePrepare
  	CSendPrepare
  	CSendCommit
  	CSendAbort
  	CReceiveCommit
  	CReceiveAbort
  	PHandlePrepare
  	PHandleCommit
  	PHandleAbort
  	PSpontaneouslyAbort
  	CReset
  	PReset
  )
  
  func (e EventType) String() string {
  	switch e {
  	case Initial:
  		return "Initial"
  	case CReceivePrepare:
  		return "CReceivePrepare"
  	case CSendPrepare:
  		return "CSendPrepare"
  	case CSendCommit:
  		return "CSendCommit"
  	case CSendAbort:
  		return "CSendAbort"
  	case CReceiveCommit:
  		return "CReceiveCommit"
  	case CReceiveAbort:
  		return "CReceiveAbort"
  	case PHandlePrepare:
  		return "PHandlePrepare"
  	case PHandleCommit:
  		return "PHandleCommit"
  	case PHandleAbort:
  		return "PHandleAbort"
  	case PSpontaneouslyAbort:
  		return "PSpontaneouslyAbort"
  	case CReset:
  		return "CReset"
  	case PReset:
  		return "PReset"
  	default:
  		panic(fmt.Sprintf("invalid %d", e))
  	}
  }
  
  type Event struct {
  	typ    EventType
  	params []any
  	state  State
  	file   string
  	line   int
  }
  
  func printParams(ps []any) string {
  	res := []string{}
  	for _, v := range ps {
  		res = append(res, fmt.Sprintf("%+v", v))
  	}
  	return strings.Join(res, ", ")
  }
  
  func (e Event) String() string {
  	return fmt.Sprintf("%s(%s);%s:%d;%+v",
  		e.typ, printParams(e.params), path.Base(e.file), e.line, e.state)
  }
  
  /*
  type Constants struct {
      %s
  }
  */
  
  type Monitor struct {
  	// the goal of extra is just to remove maintaining our own aux state,
  	// which is annoying and error-prone as it may have to be passed across several functions
  	extra  []Event
  	events []Event
  	//constants Constants
  }
  
  func New( /* constants Constants */ ) Monitor {
  	return Monitor{
  		extra:  []Event{},
  		events: []Event{},
  		//constants: constants,
  	}
  }
  
  // TODO check initial
  
  func (m *Monitor) CheckTrace() error {
  	var prev Event
  	for i, this := range m.events {
  		if i == 0 {
  			prev = this
  		}
  		switch this.typ {
  		case Initial:
  			if err := m.CheckInitial(i, Event{}, this); err != nil {
  				return err
  			}
  		case CReceivePrepare:
  			if err := m.CheckCReceivePrepare(this.params[0], i, prev, this); err != nil {
  				return err
  			}
  		case CSendPrepare:
  			if err := m.CheckCSendPrepare(this.params[0], i, prev, this); err != nil {
  				return err
  			}
  		case CSendCommit:
  			if err := m.CheckCSendCommit(this.params[0], i, prev, this); err != nil {
  				return err
  			}
  		case CSendAbort:
  			if err := m.CheckCSendAbort(this.params[0], i, prev, this); err != nil {
  				return err
  			}
  		case CReceiveCommit:
  			if err := m.CheckCReceiveCommit(this.params[0], i, prev, this); err != nil {
  				return err
  			}
  		case CReceiveAbort:
  			if err := m.CheckCReceiveAbort(this.params[0], i, prev, this); err != nil {
  				return err
  			}
  		case PHandlePrepare:
  			if err := m.CheckPHandlePrepare(this.params[0], i, prev, this); err != nil {
  				return err
  			}
  		case PHandleCommit:
  			if err := m.CheckPHandleCommit(this.params[0], i, prev, this); err != nil {
  				return err
  			}
  		case PHandleAbort:
  			if err := m.CheckPHandleAbort(this.params[0], i, prev, this); err != nil {
  				return err
  			}
  		case PSpontaneouslyAbort:
  			if err := m.CheckPSpontaneouslyAbort(this.params[0], i, prev, this); err != nil {
  				return err
  			}
  		case CReset:
  			if err := m.CheckCReset(i, prev, this); err != nil {
  				return err
  			}
  		case PReset:
  			if err := m.CheckPReset(i, prev, this); err != nil {
  				return err
  			}
  		}
  		prev = this
  	}
  	return nil
  }
  
  func (m *Monitor) ShowTrace() {
  	for i, v := range m.events {
  		fmt.Printf("%d;%+v\n", i, v)
  	}
  }
  
  func fail(format string, a ...any) error {
  	if crash {
  		panic(fmt.Sprintf(format, a...))
  	}
  	return fmt.Errorf(format, a...)
  }
  
  func (m *Monitor) CheckInitial(trace_i int, prev Event, this Event) error {
  
  	if !(!reflect.DeepEqual(this.state.msgs, map[any]bool{})) {
  		return fail("initial state precondition failed at %d; msgs = {} (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(!reflect.DeepEqual(this.state.tmAborted, []any{})) {
  		return fail("initial state precondition failed at %d; tmAborted = <<>> (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(!reflect.DeepEqual(this.state.tmCommitted, []any{})) {
  		return fail("initial state precondition failed at %d; tmCommitted = <<>> (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(!reflect.DeepEqual(this.state.lastMsgSent, []any{})) {
  		return fail("initial state precondition failed at %d; lastMsgSent = <<>> (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(!reflect.DeepEqual(this.state.tmPrepared, []any{})) {
  		return fail("initial state precondition failed at %d; tmPrepared = <<>> (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(!reflect.DeepEqual(this.state.lastMsgReceived, []any{})) {
  		return fail("initial state precondition failed at %d; lastMsgReceived = <<>> (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(!reflect.DeepEqual(this.state.rmState, map[any]any{"r1": "working", "r2": "working"})) {
  		return fail("initial state precondition failed at %d; rmState = [r1 |-> \"working\", r2 |-> \"working\"] (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(!reflect.DeepEqual(this.state.who, "none")) {
  		return fail("initial state precondition failed at %d; who = \"none\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCReceivePrepare(r any, trace_i int, prev Event, this Event) error {
  
  	_, v0 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Prepared", "rm": r}]
  	if !(v0) {
  		return fail("precondition failed at %d; Receive([\"type\" |-> \"Prepared\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v2 := map[any]bool{}
  	for _, v := range prev.state.tmPrepared.([]any) {
  		v2[v] = true
  	}
  	_, v1 := v2[r]
  	if !(!v1) {
  		return fail("precondition failed at %d; r \\notin ToSet(tmPrepared) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.tmPrepared, append(prev.state.tmPrepared.([]any), r))) {
  		return fail("postcondition failed at %d; '(tmPrepared) = Append(tmPrepared, r) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, "coordinator")) {
  		return fail("postcondition failed at %d; '(who) = \"coordinator\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgReceived, []any{map[string]any{"type": "Prepared", "rm": r}})) {
  		return fail("postcondition failed at %d; '(lastMsgReceived) = Some([\"type\" |-> \"Prepared\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgSent, []any{})) {
  		return fail("postcondition failed at %d; '(lastMsgSent) = None (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.msgs, prev.state.msgs)) {
  		return fail("precondition failed at %d; UNCHANGED(<<msgs>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed at %d; UNCHANGED(<<rmState>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.tmCommitted, prev.state.tmCommitted) && reflect.DeepEqual(this.state.tmAborted, prev.state.tmAborted)) {
  		return fail("precondition failed at %d; UNCHANGED(<<tmCommitted, tmAborted>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCSendPrepare(r any, trace_i int, prev Event, this Event) error {
  
  	v3 := map[any]bool{}
  	for _, v := range prev.state.tmPrepared.([]any) {
  		v3[v] = true
  	}
  	if !(!reflect.DeepEqual(v3, map[any]bool{})) {
  		return fail("precondition failed at %d; ToSet(tmPrepared) /= RM (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v4 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Prepare", "rm": r}]
  	v5 := map[any]bool{}
  	for v6, v7 := range prev.state.msgs.(map[any]bool) {
  		v5[v6] = v7
  	}
  	for v8, v9 := range map[any]bool{map[string]any{"type": "Prepare", "rm": r}: true} {
  		v5[v8] = v9
  	}
  	if !(!v4 && reflect.DeepEqual(this.state.msgs, v5)) {
  		return fail("precondition failed at %d; Send([\"type\" |-> \"Prepare\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, "coordinator")) {
  		return fail("postcondition failed at %d; '(who) = \"coordinator\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgReceived, []any{})) {
  		return fail("postcondition failed at %d; '(lastMsgReceived) = None (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgSent, []any{map[string]any{"type": "Prepare", "rm": r}})) {
  		return fail("postcondition failed at %d; '(lastMsgSent) = Some([\"type\" |-> \"Prepare\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed at %d; UNCHANGED(<<rmState>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !((reflect.DeepEqual(this.state.tmPrepared, prev.state.tmPrepared) && reflect.DeepEqual(this.state.tmCommitted, prev.state.tmCommitted)) && reflect.DeepEqual(this.state.tmAborted, prev.state.tmAborted)) {
  		return fail("precondition failed at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCSendCommit(r any, trace_i int, prev Event, this Event) error {
  
  	v10 := map[any]bool{}
  	for _, v := range prev.state.tmPrepared.([]any) {
  		v10[v] = true
  	}
  	if !(reflect.DeepEqual(v10, map[any]bool{})) {
  		return fail("precondition failed at %d; ToSet(tmPrepared) = RM (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v11 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Commit", "rm": r}]
  	v12 := map[any]bool{}
  	for v13, v14 := range prev.state.msgs.(map[any]bool) {
  		v12[v13] = v14
  	}
  	for v15, v16 := range map[any]bool{map[string]any{"type": "Commit", "rm": r}: true} {
  		v12[v15] = v16
  	}
  	if !(!v11 && reflect.DeepEqual(this.state.msgs, v12)) {
  		return fail("precondition failed at %d; Send([\"type\" |-> \"Commit\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, "coordinator")) {
  		return fail("postcondition failed at %d; '(who) = \"coordinator\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgReceived, []any{})) {
  		return fail("postcondition failed at %d; '(lastMsgReceived) = None (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgSent, []any{map[string]any{"type": "Commit", "rm": r}})) {
  		return fail("postcondition failed at %d; '(lastMsgSent) = Some([\"type\" |-> \"Commit\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed at %d; UNCHANGED(<<rmState>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !((reflect.DeepEqual(this.state.tmPrepared, prev.state.tmPrepared) && reflect.DeepEqual(this.state.tmCommitted, prev.state.tmCommitted)) && reflect.DeepEqual(this.state.tmAborted, prev.state.tmAborted)) {
  		return fail("precondition failed at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCSendAbort(r any, trace_i int, prev Event, this Event) error {
  
  	if !(!reflect.DeepEqual(prev.state.tmAborted, []any{})) {
  		return fail("precondition failed at %d; tmAborted /= <<>> (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v17 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Abort", "rm": r}]
  	v18 := map[any]bool{}
  	for v19, v20 := range prev.state.msgs.(map[any]bool) {
  		v18[v19] = v20
  	}
  	for v21, v22 := range map[any]bool{map[string]any{"type": "Abort", "rm": r}: true} {
  		v18[v21] = v22
  	}
  	if !(!v17 && reflect.DeepEqual(this.state.msgs, v18)) {
  		return fail("precondition failed at %d; Send([\"type\" |-> \"Abort\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, "coordinator")) {
  		return fail("postcondition failed at %d; '(who) = \"coordinator\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgReceived, []any{})) {
  		return fail("postcondition failed at %d; '(lastMsgReceived) = None (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgSent, []any{map[string]any{"type": "Abort", "rm": r}})) {
  		return fail("postcondition failed at %d; '(lastMsgSent) = Some([\"type\" |-> \"Abort\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed at %d; UNCHANGED(<<rmState>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !((reflect.DeepEqual(this.state.tmPrepared, prev.state.tmPrepared) && reflect.DeepEqual(this.state.tmCommitted, prev.state.tmCommitted)) && reflect.DeepEqual(this.state.tmAborted, prev.state.tmAborted)) {
  		return fail("precondition failed at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCReceiveCommit(r any, trace_i int, prev Event, this Event) error {
  
  	_, v23 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Committed", "rm": r}]
  	if !(v23) {
  		return fail("precondition failed at %d; Receive([\"type\" |-> \"Committed\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v25 := map[any]bool{}
  	for _, v := range prev.state.tmCommitted.([]any) {
  		v25[v] = true
  	}
  	_, v24 := v25[r]
  	if !(!v24) {
  		return fail("precondition failed at %d; r \\notin ToSet(tmCommitted) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, "coordinator")) {
  		return fail("postcondition failed at %d; '(who) = \"coordinator\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.tmCommitted, append(prev.state.tmCommitted.([]any), r))) {
  		return fail("postcondition failed at %d; '(tmCommitted) = Append(tmCommitted, r) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgReceived, []any{map[string]any{"type": "Committed", "rm": r}})) {
  		return fail("postcondition failed at %d; '(lastMsgReceived) = Some([\"type\" |-> \"Committed\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgSent, []any{})) {
  		return fail("postcondition failed at %d; '(lastMsgSent) = None (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed at %d; UNCHANGED(<<rmState>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !((reflect.DeepEqual(this.state.tmPrepared, prev.state.tmPrepared) && reflect.DeepEqual(this.state.msgs, prev.state.msgs)) && reflect.DeepEqual(this.state.tmAborted, prev.state.tmAborted)) {
  		return fail("precondition failed at %d; UNCHANGED(<<tmPrepared, msgs, tmAborted>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCReceiveAbort(r any, trace_i int, prev Event, this Event) error {
  
  	_, v26 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Aborted", "rm": r}]
  	if !(v26) {
  		return fail("precondition failed at %d; Receive([\"type\" |-> \"Aborted\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v28 := map[any]bool{}
  	for _, v := range prev.state.tmAborted.([]any) {
  		v28[v] = true
  	}
  	_, v27 := v28[r]
  	if !(!v27) {
  		return fail("precondition failed at %d; r \\notin ToSet(tmAborted) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, "coordinator")) {
  		return fail("postcondition failed at %d; '(who) = \"coordinator\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.tmAborted, append(prev.state.tmAborted.([]any), r))) {
  		return fail("postcondition failed at %d; '(tmAborted) = Append(tmAborted, r) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgReceived, []any{map[string]any{"type": "Aborted", "rm": r}})) {
  		return fail("postcondition failed at %d; '(lastMsgReceived) = Some([\"type\" |-> \"Aborted\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgSent, []any{})) {
  		return fail("postcondition failed at %d; '(lastMsgSent) = None (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed at %d; UNCHANGED(<<rmState>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !((reflect.DeepEqual(this.state.tmPrepared, prev.state.tmPrepared) && reflect.DeepEqual(this.state.msgs, prev.state.msgs)) && reflect.DeepEqual(this.state.tmCommitted, prev.state.tmCommitted)) {
  		return fail("precondition failed at %d; UNCHANGED(<<tmPrepared, msgs, tmCommitted>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckPHandlePrepare(r any, trace_i int, prev Event, this Event) error {
  
  	if !(reflect.DeepEqual(prev.state.rmState.(map[any]any)[r], "working")) {
  		return fail("precondition failed at %d; rmState[r] = \"working\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v29 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Prepare", "rm": r}]
  	if !(v29) {
  		return fail("precondition failed at %d; Receive([\"type\" |-> \"Prepare\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v30 := map[any]any{}
  	for v31, v32 := range prev.state.rmState.(map[any]any) {
  		v30[v31] = v32
  	}
  	v30[r] = "prepared"
  	if !(reflect.DeepEqual(this.state.rmState, v30)) {
  		return fail("postcondition failed at %d; '(rmState) = [rmState EXCEPT ![r] = \"prepared\"] (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v33 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Prepared", "rm": r}]
  	v34 := map[any]bool{}
  	for v35, v36 := range prev.state.msgs.(map[any]bool) {
  		v34[v35] = v36
  	}
  	for v37, v38 := range map[any]bool{map[string]any{"type": "Prepared", "rm": r}: true} {
  		v34[v37] = v38
  	}
  	if !(!v33 && reflect.DeepEqual(this.state.msgs, v34)) {
  		return fail("precondition failed at %d; Send([\"type\" |-> \"Prepared\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, r)) {
  		return fail("postcondition failed at %d; '(who) = r (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgReceived, prev.state.lastMsgReceived) && reflect.DeepEqual(this.state.lastMsgSent, prev.state.lastMsgSent)) {
  		return fail("precondition failed at %d; UNCHANGED(<<lastMsgReceived, lastMsgSent>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !((reflect.DeepEqual(this.state.tmPrepared, prev.state.tmPrepared) && reflect.DeepEqual(this.state.tmCommitted, prev.state.tmCommitted)) && reflect.DeepEqual(this.state.tmAborted, prev.state.tmAborted)) {
  		return fail("precondition failed at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckPHandleCommit(r any, trace_i int, prev Event, this Event) error {
  
  	if !(reflect.DeepEqual(prev.state.rmState.(map[any]any)[r], "prepared")) {
  		return fail("precondition failed at %d; rmState[r] = \"prepared\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v39 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Commit", "rm": r}]
  	if !(v39) {
  		return fail("precondition failed at %d; Receive([\"type\" |-> \"Commit\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v40 := map[any]any{}
  	for v41, v42 := range prev.state.rmState.(map[any]any) {
  		v40[v41] = v42
  	}
  	v40[r] = "committed"
  	if !(reflect.DeepEqual(this.state.rmState, v40)) {
  		return fail("postcondition failed at %d; '(rmState) = [rmState EXCEPT ![r] = \"committed\"] (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v43 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Committed", "rm": r}]
  	v44 := map[any]bool{}
  	for v45, v46 := range prev.state.msgs.(map[any]bool) {
  		v44[v45] = v46
  	}
  	for v47, v48 := range map[any]bool{map[string]any{"type": "Committed", "rm": r}: true} {
  		v44[v47] = v48
  	}
  	if !(!v43 && reflect.DeepEqual(this.state.msgs, v44)) {
  		return fail("precondition failed at %d; Send([\"type\" |-> \"Committed\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, r)) {
  		return fail("postcondition failed at %d; '(who) = r (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgReceived, prev.state.lastMsgReceived) && reflect.DeepEqual(this.state.lastMsgSent, prev.state.lastMsgSent)) {
  		return fail("precondition failed at %d; UNCHANGED(<<lastMsgReceived, lastMsgSent>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !((reflect.DeepEqual(this.state.tmPrepared, prev.state.tmPrepared) && reflect.DeepEqual(this.state.tmCommitted, prev.state.tmCommitted)) && reflect.DeepEqual(this.state.tmAborted, prev.state.tmAborted)) {
  		return fail("precondition failed at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckPHandleAbort(r any, trace_i int, prev Event, this Event) error {
  
  	_, v49 := map[any]bool{"working": true, "prepared": true}[prev.state.rmState.(map[any]any)[r]]
  	if !(v49) {
  		return fail("precondition failed at %d; rmState[r] \\in {\"working\", \"prepared\"} (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v50 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Abort", "rm": r}]
  	if !(v50) {
  		return fail("precondition failed at %d; Receive([\"type\" |-> \"Abort\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v51 := map[any]any{}
  	for v52, v53 := range prev.state.rmState.(map[any]any) {
  		v51[v52] = v53
  	}
  	v51[r] = "aborted"
  	if !(reflect.DeepEqual(this.state.rmState, v51)) {
  		return fail("postcondition failed at %d; '(rmState) = [rmState EXCEPT ![r] = \"aborted\"] (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, r)) {
  		return fail("postcondition failed at %d; '(who) = r (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v54 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Aborted", "rm": r}]
  	v55 := map[any]bool{}
  	for v56, v57 := range prev.state.msgs.(map[any]bool) {
  		v55[v56] = v57
  	}
  	for v58, v59 := range map[any]bool{map[string]any{"type": "Aborted", "rm": r}: true} {
  		v55[v58] = v59
  	}
  	if !(!v54 && reflect.DeepEqual(this.state.msgs, v55)) {
  		return fail("precondition failed at %d; Send([\"type\" |-> \"Aborted\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgReceived, prev.state.lastMsgReceived) && reflect.DeepEqual(this.state.lastMsgSent, prev.state.lastMsgSent)) {
  		return fail("precondition failed at %d; UNCHANGED(<<lastMsgReceived, lastMsgSent>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !((reflect.DeepEqual(this.state.tmPrepared, prev.state.tmPrepared) && reflect.DeepEqual(this.state.tmCommitted, prev.state.tmCommitted)) && reflect.DeepEqual(this.state.tmAborted, prev.state.tmAborted)) {
  		return fail("precondition failed at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckPSpontaneouslyAbort(r any, trace_i int, prev Event, this Event) error {
  
  	_, v60 := map[any]bool{"working": true, "prepared": true}[prev.state.rmState.(map[any]any)[r]]
  	if !(v60) {
  		return fail("precondition failed at %d; rmState[r] \\in {\"working\", \"prepared\"} (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v61 := map[any]any{}
  	for v62, v63 := range prev.state.rmState.(map[any]any) {
  		v61[v62] = v63
  	}
  	v61[r] = "aborted"
  	if !(reflect.DeepEqual(this.state.rmState, v61)) {
  		return fail("postcondition failed at %d; '(rmState) = [rmState EXCEPT ![r] = \"aborted\"] (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, r)) {
  		return fail("postcondition failed at %d; '(who) = r (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v64 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Aborted", "rm": r}]
  	v65 := map[any]bool{}
  	for v66, v67 := range prev.state.msgs.(map[any]bool) {
  		v65[v66] = v67
  	}
  	for v68, v69 := range map[any]bool{map[string]any{"type": "Aborted", "rm": r}: true} {
  		v65[v68] = v69
  	}
  	if !(!v64 && reflect.DeepEqual(this.state.msgs, v65)) {
  		return fail("precondition failed at %d; Send([\"type\" |-> \"Aborted\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgReceived, prev.state.lastMsgReceived) && reflect.DeepEqual(this.state.lastMsgSent, prev.state.lastMsgSent)) {
  		return fail("precondition failed at %d; UNCHANGED(<<lastMsgReceived, lastMsgSent>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !((reflect.DeepEqual(this.state.tmPrepared, prev.state.tmPrepared) && reflect.DeepEqual(this.state.tmCommitted, prev.state.tmCommitted)) && reflect.DeepEqual(this.state.tmAborted, prev.state.tmAborted)) {
  		return fail("precondition failed at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCReset(trace_i int, prev Event, this Event) error {
  
  	v70 := true
  	for v71, _ := range map[any]bool{} {
  		_, v72 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Committed", "rm": v71}]
  		v70 = v70 && v72
  	}
  	if !(v70) {
  
  		v73 := true
  		for v74, _ := range map[any]bool{} {
  			_, v75 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Aborted", "rm": v74}]
  			v73 = v73 && v75
  		}
  		if !(v73) {
  
  			v73 := true
  			for v74, _ := range map[any]bool{} {
  				_, v75 := prev.state.msgs.(map[any]bool)[map[string]any{"type": "Aborted", "rm": v74}]
  				v73 = v73 && v75
  			}
  			if !(v73) {
  				return fail("precondition failed at %d; (\\A r \\in RM : [\"type\" |-> \"Committed\", \"rm\" |-> r] \\in msgs \\/ \\A r \\in RM : [\"type\" |-> \"Aborted\", \"rm\" |-> r] \\in msgs) (prev: %+v, this: %+v)", trace_i, prev, this)
  			}
  		}
  
  	}
  
  	if !(reflect.DeepEqual(this.state.lastMsgReceived, []any{})) {
  		return fail("postcondition failed at %d; '(lastMsgReceived) = None (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgSent, []any{})) {
  		return fail("postcondition failed at %d; '(lastMsgSent) = None (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.tmPrepared, []any{})) {
  		return fail("postcondition failed at %d; '(tmPrepared) = <<>> (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.tmCommitted, []any{})) {
  		return fail("postcondition failed at %d; '(tmCommitted) = <<>> (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.tmAborted, []any{})) {
  		return fail("postcondition failed at %d; '(tmAborted) = <<>> (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.msgs, map[any]bool{})) {
  		return fail("postcondition failed at %d; '(msgs) = {} (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed at %d; UNCHANGED(<<rmState>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckPReset(trace_i int, prev Event, this Event) error {
  
  	v76 := true
  	for v77, _ := range map[any]bool{} {
  		v76 = v76 && reflect.DeepEqual(prev.state.rmState.(map[any]any)[v77], "aborted")
  	}
  	if !(v76) {
  
  		v78 := true
  		for v79, _ := range map[any]bool{} {
  			v78 = v78 && reflect.DeepEqual(prev.state.rmState.(map[any]any)[v79], "committed")
  		}
  		if !(v78) {
  
  			v78 := true
  			for v79, _ := range map[any]bool{} {
  				v78 = v78 && reflect.DeepEqual(prev.state.rmState.(map[any]any)[v79], "committed")
  			}
  			if !(v78) {
  				return fail("precondition failed at %d; (\\A r \\in RM : rmState[r] = \"aborted\" \\/ \\A r \\in RM : rmState[r] = \"committed\") (prev: %+v, this: %+v)", trace_i, prev, this)
  			}
  		}
  
  	}
  
  	v80 := map[any]any{}
  	for v81, _ := range map[any]bool{} {
  		v80[v81] = "working"
  	}
  
  	if !(reflect.DeepEqual(this.state.rmState, v80)) {
  		return fail("postcondition failed at %d; '(rmState) = [ r \\in RM |-> \"working\" ] (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, "none")) {
  		return fail("postcondition failed at %d; '(who) = \"none\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgReceived, prev.state.lastMsgReceived) && reflect.DeepEqual(this.state.lastMsgSent, prev.state.lastMsgSent)) {
  		return fail("precondition failed at %d; UNCHANGED(<<lastMsgReceived, lastMsgSent>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !((reflect.DeepEqual(this.state.tmPrepared, prev.state.tmPrepared) && reflect.DeepEqual(this.state.tmCommitted, prev.state.tmCommitted)) && reflect.DeepEqual(this.state.tmAborted, prev.state.tmAborted)) {
  		return fail("precondition failed at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.msgs, prev.state.msgs)) {
  		return fail("precondition failed at %d; UNCHANGED(<<msgs>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  /* Action t1 cannot be translated because of: ToTrace(CounterExample) */
  
  /* Action Post cannot be translated because of: ToTrace(CounterExample) */
  
  /*
  func (m *Monitor) CheckInc(i int, prev Event, this Event) error {
  
  	if prev.state.x.(int) <= 0 {
  		return fail("precondition failed at %d; expected x <= 0 but got %s (prev: %+v, this: %+v)", i, prev.state.x, prev, this)
  	}
  	// check that new values are allowed
  	if this.state.x != prev.state.x.(int)+1 { // for each var
  		return fail("postcondition violated for x at %d; should be %+v but got %+v (prev: %+v, this: %+v)", i,
  			prev.state.x.(int)+1, this.state.x, prev, this)
  	}
  
  	// check unchanged
  	if this.state.x != prev.state.x { // for each var
  		return fail("unchanged violated for x at %d; expected x to remain as %+v but it is %+v (prev: %+v, this: %+v)", i, prev.state.x, this.state.x, prev, this)
  	}
  
  	return nil
  }
  */
  
  // this state value can have nil fields
  func (m *Monitor) CaptureVariable(v State, typ EventType, args ...any) error {
  
  	e := Event{
  		typ:    typ,
  		params: args,
  		state:  v,
  		// no need to capture file and line here
  	}
  	m.extra = append(m.extra, e)
  	return nil
  }
  
  func (m *Monitor) CaptureState(c State, typ EventType, args ...any) error {
  
  	// override current values with extras
  	// all have to pertain to this action
  	for _, v := range m.extra {
  		// sanity checks
  		if v.typ != typ {
  			return fmt.Errorf("type did not match")
  		}
  		for i, p := range v.params {
  			if p != args[i] {
  				return fmt.Errorf("arg %d did not match", i)
  			}
  		}
  		// there is no null in TLA+, and also all the struct fields are any, which are reference types
  
  		// for each variable in state
  		if v.state.who != nil {
  			c.who = v.state.who
  		}
  		if v.state.lastMsgReceived != nil {
  			c.lastMsgReceived = v.state.lastMsgReceived
  		}
  		if v.state.tmCommitted != nil {
  			c.tmCommitted = v.state.tmCommitted
  		}
  		if v.state.lastMsgSent != nil {
  			c.lastMsgSent = v.state.lastMsgSent
  		}
  		if v.state.tmPrepared != nil {
  			c.tmPrepared = v.state.tmPrepared
  		}
  		if v.state.msgs != nil {
  			c.msgs = v.state.msgs
  		}
  		if v.state.tmAborted != nil {
  			c.tmAborted = v.state.tmAborted
  		}
  		if v.state.rmState != nil {
  			c.rmState = v.state.rmState
  		}
  	}
  
  	// reset
  	m.extra = []Event{}
  
  	// record event
  	file, line := getFileLine()
  	e := Event{
  		typ:    typ,
  		params: args,
  		state:  c,
  		file:   file,
  		line:   line,
  	}
  
  	m.events = append(m.events, e)
  
  	return nil
  }
