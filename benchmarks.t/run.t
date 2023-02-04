
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
  	"encoding/json"
  	"fmt"
  	"path"
  	"reflect"
  	"runtime"
  	"strings"
  )
  
  type set = map[string]any
  type record = map[string]any
  type seq = []any
  
  // panic instead of returning error
  var crash = true
  
  func hash(a any) string {
  	s, _ := json.Marshal(a)
  	return string(s)
  }
  
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
  
  	if !(reflect.DeepEqual(this.state.x, 1)) {
  		return fail("initial state precondition failed at %d; x = 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckA(trace_i int, prev Event, this Event) error {
  
  	if !(reflect.DeepEqual(this.state.x, (any(prev.state.x).(int) + 1))) {
  		return fail("postcondition failed at %d; '(x) = x + 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckConstr(trace_i int, prev Event, this Event) error {
  
  	if !(any(prev.state.x).(int) < 2) {
  		return fail("precondition failed at %d; x < 2 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckInv(trace_i int, prev Event, this Event) error {
  
  	if !(any(prev.state.x).(int) < 3) {
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
  	"encoding/json"
  	"fmt"
  	"path"
  	"reflect"
  	"runtime"
  	"strings"
  )
  
  type set = map[string]any
  type record = map[string]any
  type seq = []any
  
  // panic instead of returning error
  var crash = true
  
  func hash(a any) string {
  	s, _ := json.Marshal(a)
  	return string(s)
  }
  
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
  	Sets
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
  	case Sets:
  		return "Sets"
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
  		case Sets:
  			if err := m.CheckSets(i, prev, this); err != nil {
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
  
  	if !(reflect.DeepEqual(this.state.x, 1)) {
  		return fail("initial state precondition failed at %d; x = 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckA(trace_i int, prev Event, this Event) error {
  
  	if !(any(prev.state.x).(int) < 0) {
  		return fail("precondition failed at %d; x < 0 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.x, (any(prev.state.x).(int) + 1))) {
  		return fail("postcondition failed at %d; '(x) = x + 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckA1(trace_i int, prev Event, this Event) error {
  
  	if !(any(prev.state.x).(int) < 0) {
  		return fail("precondition failed at %d; x < 0 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.x, (any(prev.state.x).(int)+1)) && (any(prev.state.x).(int) < 0)) {
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
  
  	v0_except := map[any]any{}
  	for v1, v2 := range map[string]any{"a": 1} {
  		v0_except[v1] = v2
  	}
  	v0_except["a"] = 2
  	if !(reflect.DeepEqual(v0_except["a"], 2)) {
  		return fail("precondition failed at %d; [[\"a\" |-> 1] EXCEPT ![\"a\"] = 2][\"a\"] = 2 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckH(trace_i int, prev Event, this Event) error {
  
  	v3_setliteral := map[string]any{}
  	v3_setliteral[hash(1)] = 1
  	v3_setliteral[hash(2)] = 2
  	v4_boundedforall := true
  	for v5, _ := range v3_setliteral {
  		v3_setliteral := map[string]any{}
  		v3_setliteral[hash(1)] = 1
  		v3_setliteral[hash(2)] = 2
  		v4_boundedforall = v4_boundedforall && reflect.DeepEqual(v5, 1)
  	}
  	if !(v4_boundedforall) {
  		return fail("precondition failed at %d; \\A r \\in {1, 2} : r = 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckH1(trace_i int, prev Event, this Event) error {
  
  	v6_setliteral := map[string]any{}
  	v6_setliteral[hash(1)] = 1
  	v6_setliteral[hash(2)] = 2
  	v7_boundedforall := true
  	for v8, _ := range v6_setliteral {
  		v6_setliteral := map[string]any{}
  		v6_setliteral[hash(1)] = 1
  		v6_setliteral[hash(2)] = 2
  		v9_setliteral := map[string]any{}
  		v9_setliteral[hash(3)] = 3
  		v9_setliteral[hash(4)] = 4
  		v10_boundedforall := true
  		for v11, _ := range v9_setliteral {
  			v9_setliteral := map[string]any{}
  			v9_setliteral[hash(3)] = 3
  			v9_setliteral[hash(4)] = 4
  			v10_boundedforall = v10_boundedforall && reflect.DeepEqual(v11, v8)
  		}
  		v7_boundedforall = v7_boundedforall && v10_boundedforall
  	}
  	if !(v7_boundedforall) {
  		return fail("precondition failed at %d; \\A s \\in {1, 2} : \\A r \\in {3, 4} : r = s (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckH2(trace_i int, prev Event, this Event) error {
  
  	v15_setlit := map[string]any{}
  	v15_setlit[hash("s1")] = "s1"
  	v15_setlit[hash("2")] = "2"
  	v12_fnconstr := map[any]any{}
  	for v13, _ := range v15_setlit {
  		v12_fnconstr[v13] = "a"
  	}
  
  	if !(reflect.DeepEqual(v12_fnconstr["a"], 1)) {
  		return fail("precondition failed at %d; [ r \\in RM |-> \"a\" ][\"a\"] = 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckH3(trace_i int, prev Event, this Event) error {
  
  	v19_setlit := map[string]any{}
  	v19_setlit[hash("s1")] = "s1"
  	v19_setlit[hash("2")] = "2"
  	v16_fnconstr := map[any]any{}
  	for v17, v18 := range v19_setlit {
  		v16_fnconstr[v17] = any(v18).(set)
  	}
  
  	if !(reflect.DeepEqual(v16_fnconstr["a"], 1)) {
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
  	if !(reflect.DeepEqual(((any(a).(int) + any(b).(int)) + any(c).(int)), 1)) {
  		return fail("precondition failed at %d; a + b + c = 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckSets(trace_i int, prev Event, this Event) error {
  
  	v25_setliteral := map[string]any{}
  	v25_setliteral[hash(1)] = 1
  	v25_setliteral[hash(2)] = 2
  	v26_setliteral := map[string]any{}
  	v26_setliteral[hash(3)] = 3
  	v20_union := map[string]any{}
  	for v21, v22 := range v25_setliteral {
  		v20_union[v21] = v22
  	}
  	for v23, v24 := range v26_setliteral {
  		v20_union[v23] = v24
  	}
  	v27_setliteral := map[string]any{}
  	if !(reflect.DeepEqual(v20_union, v27_setliteral)) {
  		return fail("precondition failed at %d; {1, 2} \\union {3} = {} (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v29_setliteral := map[string]any{}
  	v29_setliteral[hash(3)] = 3
  	_, v28_notin := v29_setliteral[hash(1)]
  	if !(!v28_notin) {
  		return fail("precondition failed at %d; 1 \\notin {3} (prev: %+v, this: %+v)", trace_i, prev, this)
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
  	"encoding/json"
  	"fmt"
  	"path"
  	"reflect"
  	"runtime"
  	"strings"
  )
  
  type set = map[string]any
  type record = map[string]any
  type seq = []any
  
  // panic instead of returning error
  var crash = true
  
  func hash(a any) string {
  	s, _ := json.Marshal(a)
  	return string(s)
  }
  
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
  
  	if !(reflect.DeepEqual(this.state.x, 1)) {
  		return fail("initial state precondition failed at %d; x = 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckA(trace_i int, prev Event, this Event) error {
  
  	if !(reflect.DeepEqual(this.state.x, (any(prev.state.x).(int) + 1))) {
  		return fail("postcondition failed at %d; '(x) = x + 1 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckConstr(trace_i int, prev Event, this Event) error {
  
  	if !(any(prev.state.x).(int) < 2) {
  		return fail("precondition failed at %d; x < 2 (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckInv(trace_i int, prev Event, this Event) error {
  
  	if !(any(prev.state.x).(int) < 3) {
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
  	"encoding/json"
  	"fmt"
  	"path"
  	"reflect"
  	"runtime"
  	"strings"
  )
  
  type set = map[string]any
  type record = map[string]any
  type seq = []any
  
  // panic instead of returning error
  var crash = true
  
  func hash(a any) string {
  	s, _ := json.Marshal(a)
  	return string(s)
  }
  
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
  
  	v100_setlit := map[string]any{}
  	if !(reflect.DeepEqual(this.state.msgs, v100_setlit)) {
  		return fail("initial state precondition failed at %d; msgs = {} (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.tmAborted, []any{})) {
  		return fail("initial state precondition failed at %d; tmAborted = <<>> (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.tmCommitted, []any{})) {
  		return fail("initial state precondition failed at %d; tmCommitted = <<>> (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgSent, []any{})) {
  		return fail("initial state precondition failed at %d; lastMsgSent = <<>> (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.tmPrepared, []any{})) {
  		return fail("initial state precondition failed at %d; tmPrepared = <<>> (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.lastMsgReceived, []any{})) {
  		return fail("initial state precondition failed at %d; lastMsgReceived = <<>> (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.rmState, map[any]any{"r1": "working", "r2": "working"})) {
  		return fail("initial state precondition failed at %d; rmState = [r1 |-> \"working\", r2 |-> \"working\"] (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, "none")) {
  		return fail("initial state precondition failed at %d; who = \"none\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCReceivePrepare(r any, trace_i int, prev Event, this Event) error {
  
  	_, v0_in := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Prepared", "rm": r})]
  	if !(v0_in) {
  		return fail("precondition failed at %d; Receive([\"type\" |-> \"Prepared\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v2_toset := map[any]bool{}
  	for _, v := range any(prev.state.tmPrepared).(seq) {
  		v2_toset[v] = true
  	}
  	_, v1_notin := v2_toset[hash(r)]
  	if !(!v1_notin) {
  		return fail("precondition failed at %d; r \\notin ToSet(tmPrepared) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.tmPrepared, append(any(prev.state.tmPrepared).(seq), any(r).(seq)))) {
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
  
  	v3_toset := map[any]bool{}
  	for _, v := range any(prev.state.tmPrepared).(seq) {
  		v3_toset[v] = true
  	}
  	v4_setlit := map[string]any{}
  	v4_setlit[hash("r1")] = "r1"
  	v4_setlit[hash("r2")] = "r2"
  	if !(!reflect.DeepEqual(v3_toset, v4_setlit)) {
  		return fail("precondition failed at %d; ToSet(tmPrepared) /= RM (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v5_notin := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Prepare", "rm": r})]
  	v11_setliteral := map[string]any{}
  	v11_setliteral[hash(map[string]any{"type": "Prepare", "rm": any(r).(set)})] = map[string]any{"type": "Prepare", "rm": any(r).(set)}
  	v6_union := map[string]any{}
  	for v7, v8 := range any(prev.state.msgs).(set) {
  		v6_union[v7] = v8
  	}
  	for v9, v10 := range v11_setliteral {
  		v6_union[v9] = v10
  	}
  	if !(!v5_notin && reflect.DeepEqual(this.state.msgs, v6_union)) {
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
  
  	v12_toset := map[any]bool{}
  	for _, v := range any(prev.state.tmPrepared).(seq) {
  		v12_toset[v] = true
  	}
  	v13_setlit := map[string]any{}
  	v13_setlit[hash("r1")] = "r1"
  	v13_setlit[hash("r2")] = "r2"
  	if !(reflect.DeepEqual(v12_toset, v13_setlit)) {
  		return fail("precondition failed at %d; ToSet(tmPrepared) = RM (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v14_notin := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Commit", "rm": r})]
  	v20_setliteral := map[string]any{}
  	v20_setliteral[hash(map[string]any{"type": "Commit", "rm": any(r).(set)})] = map[string]any{"type": "Commit", "rm": any(r).(set)}
  	v15_union := map[string]any{}
  	for v16, v17 := range any(prev.state.msgs).(set) {
  		v15_union[v16] = v17
  	}
  	for v18, v19 := range v20_setliteral {
  		v15_union[v18] = v19
  	}
  	if !(!v14_notin && reflect.DeepEqual(this.state.msgs, v15_union)) {
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
  	_, v21_notin := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Abort", "rm": r})]
  	v27_setliteral := map[string]any{}
  	v27_setliteral[hash(map[string]any{"type": "Abort", "rm": any(r).(set)})] = map[string]any{"type": "Abort", "rm": any(r).(set)}
  	v22_union := map[string]any{}
  	for v23, v24 := range any(prev.state.msgs).(set) {
  		v22_union[v23] = v24
  	}
  	for v25, v26 := range v27_setliteral {
  		v22_union[v25] = v26
  	}
  	if !(!v21_notin && reflect.DeepEqual(this.state.msgs, v22_union)) {
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
  
  	_, v28_in := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Committed", "rm": r})]
  	if !(v28_in) {
  		return fail("precondition failed at %d; Receive([\"type\" |-> \"Committed\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v30_toset := map[any]bool{}
  	for _, v := range any(prev.state.tmCommitted).(seq) {
  		v30_toset[v] = true
  	}
  	_, v29_notin := v30_toset[hash(r)]
  	if !(!v29_notin) {
  		return fail("precondition failed at %d; r \\notin ToSet(tmCommitted) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, "coordinator")) {
  		return fail("postcondition failed at %d; '(who) = \"coordinator\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.tmCommitted, append(any(prev.state.tmCommitted).(seq), any(r).(seq)))) {
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
  
  	_, v31_in := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Aborted", "rm": r})]
  	if !(v31_in) {
  		return fail("precondition failed at %d; Receive([\"type\" |-> \"Aborted\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v33_toset := map[any]bool{}
  	for _, v := range any(prev.state.tmAborted).(seq) {
  		v33_toset[v] = true
  	}
  	_, v32_notin := v33_toset[hash(r)]
  	if !(!v32_notin) {
  		return fail("precondition failed at %d; r \\notin ToSet(tmAborted) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, "coordinator")) {
  		return fail("postcondition failed at %d; '(who) = \"coordinator\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.tmAborted, append(any(prev.state.tmAborted).(seq), any(r).(seq)))) {
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
  
  	if !(reflect.DeepEqual(any(prev.state.rmState).(record)[any(r).(string)], "working")) {
  		return fail("precondition failed at %d; rmState[r] = \"working\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v34_in := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Prepare", "rm": r})]
  	if !(v34_in) {
  		return fail("precondition failed at %d; Receive([\"type\" |-> \"Prepare\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v35_except := map[any]any{}
  	for v36, v37 := range any(prev.state.rmState).(record) {
  		v35_except[v36] = v37
  	}
  	v35_except[r] = "prepared"
  	if !(reflect.DeepEqual(this.state.rmState, v35_except)) {
  		return fail("postcondition failed at %d; '(rmState) = [rmState EXCEPT ![r] = \"prepared\"] (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v38_notin := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Prepared", "rm": r})]
  	v44_setliteral := map[string]any{}
  	v44_setliteral[hash(map[string]any{"type": "Prepared", "rm": any(r).(set)})] = map[string]any{"type": "Prepared", "rm": any(r).(set)}
  	v39_union := map[string]any{}
  	for v40, v41 := range any(prev.state.msgs).(set) {
  		v39_union[v40] = v41
  	}
  	for v42, v43 := range v44_setliteral {
  		v39_union[v42] = v43
  	}
  	if !(!v38_notin && reflect.DeepEqual(this.state.msgs, v39_union)) {
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
  
  	if !(reflect.DeepEqual(any(prev.state.rmState).(record)[any(r).(string)], "prepared")) {
  		return fail("precondition failed at %d; rmState[r] = \"prepared\" (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v45_in := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Commit", "rm": r})]
  	if !(v45_in) {
  		return fail("precondition failed at %d; Receive([\"type\" |-> \"Commit\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v46_except := map[any]any{}
  	for v47, v48 := range any(prev.state.rmState).(record) {
  		v46_except[v47] = v48
  	}
  	v46_except[r] = "committed"
  	if !(reflect.DeepEqual(this.state.rmState, v46_except)) {
  		return fail("postcondition failed at %d; '(rmState) = [rmState EXCEPT ![r] = \"committed\"] (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v49_notin := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Committed", "rm": r})]
  	v55_setliteral := map[string]any{}
  	v55_setliteral[hash(map[string]any{"type": "Committed", "rm": any(r).(set)})] = map[string]any{"type": "Committed", "rm": any(r).(set)}
  	v50_union := map[string]any{}
  	for v51, v52 := range any(prev.state.msgs).(set) {
  		v50_union[v51] = v52
  	}
  	for v53, v54 := range v55_setliteral {
  		v50_union[v53] = v54
  	}
  	if !(!v49_notin && reflect.DeepEqual(this.state.msgs, v50_union)) {
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
  
  	v57_setliteral := map[string]any{}
  	v57_setliteral[hash("working")] = "working"
  	v57_setliteral[hash("prepared")] = "prepared"
  	_, v56_in := v57_setliteral[hash(any(prev.state.rmState).(record)[any(r).(string)])]
  	if !(v56_in) {
  		return fail("precondition failed at %d; rmState[r] \\in {\"working\", \"prepared\"} (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v58_in := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Abort", "rm": r})]
  	if !(v58_in) {
  		return fail("precondition failed at %d; Receive([\"type\" |-> \"Abort\", \"rm\" |-> r]) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v59_except := map[any]any{}
  	for v60, v61 := range any(prev.state.rmState).(record) {
  		v59_except[v60] = v61
  	}
  	v59_except[r] = "aborted"
  	if !(reflect.DeepEqual(this.state.rmState, v59_except)) {
  		return fail("postcondition failed at %d; '(rmState) = [rmState EXCEPT ![r] = \"aborted\"] (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, r)) {
  		return fail("postcondition failed at %d; '(who) = r (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v62_notin := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Aborted", "rm": r})]
  	v68_setliteral := map[string]any{}
  	v68_setliteral[hash(map[string]any{"type": "Aborted", "rm": any(r).(set)})] = map[string]any{"type": "Aborted", "rm": any(r).(set)}
  	v63_union := map[string]any{}
  	for v64, v65 := range any(prev.state.msgs).(set) {
  		v63_union[v64] = v65
  	}
  	for v66, v67 := range v68_setliteral {
  		v63_union[v66] = v67
  	}
  	if !(!v62_notin && reflect.DeepEqual(this.state.msgs, v63_union)) {
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
  
  	v70_setliteral := map[string]any{}
  	v70_setliteral[hash("working")] = "working"
  	v70_setliteral[hash("prepared")] = "prepared"
  	_, v69_in := v70_setliteral[hash(any(prev.state.rmState).(record)[any(r).(string)])]
  	if !(v69_in) {
  		return fail("precondition failed at %d; rmState[r] \\in {\"working\", \"prepared\"} (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	v71_except := map[any]any{}
  	for v72, v73 := range any(prev.state.rmState).(record) {
  		v71_except[v72] = v73
  	}
  	v71_except[r] = "aborted"
  	if !(reflect.DeepEqual(this.state.rmState, v71_except)) {
  		return fail("postcondition failed at %d; '(rmState) = [rmState EXCEPT ![r] = \"aborted\"] (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.who, r)) {
  		return fail("postcondition failed at %d; '(who) = r (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	_, v74_notin := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Aborted", "rm": r})]
  	v80_setliteral := map[string]any{}
  	v80_setliteral[hash(map[string]any{"type": "Aborted", "rm": any(r).(set)})] = map[string]any{"type": "Aborted", "rm": any(r).(set)}
  	v75_union := map[string]any{}
  	for v76, v77 := range any(prev.state.msgs).(set) {
  		v75_union[v76] = v77
  	}
  	for v78, v79 := range v80_setliteral {
  		v75_union[v78] = v79
  	}
  	if !(!v74_notin && reflect.DeepEqual(this.state.msgs, v75_union)) {
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
  
  	v81_setlit := map[string]any{}
  	v81_setlit[hash("r1")] = "r1"
  	v81_setlit[hash("r2")] = "r2"
  	v82_boundedforall := true
  	for v83, _ := range v81_setlit {
  		v81_setlit := map[string]any{}
  		v81_setlit[hash("r1")] = "r1"
  		v81_setlit[hash("r2")] = "r2"
  		_, v84_in := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Committed", "rm": v83})]
  		v82_boundedforall = v82_boundedforall && v84_in
  	}
  	if !(v82_boundedforall) {
  
  		v85_setlit := map[string]any{}
  		v85_setlit[hash("r1")] = "r1"
  		v85_setlit[hash("r2")] = "r2"
  		v86_boundedforall := true
  		for v87, _ := range v85_setlit {
  			v85_setlit := map[string]any{}
  			v85_setlit[hash("r1")] = "r1"
  			v85_setlit[hash("r2")] = "r2"
  			_, v88_in := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Aborted", "rm": v87})]
  			v86_boundedforall = v86_boundedforall && v88_in
  		}
  		if !(v86_boundedforall) {
  
  			v85_setlit := map[string]any{}
  			v85_setlit[hash("r1")] = "r1"
  			v85_setlit[hash("r2")] = "r2"
  			v86_boundedforall := true
  			for v87, _ := range v85_setlit {
  				v85_setlit := map[string]any{}
  				v85_setlit[hash("r1")] = "r1"
  				v85_setlit[hash("r2")] = "r2"
  				_, v88_in := any(prev.state.msgs).(set)[hash(map[string]any{"type": "Aborted", "rm": v87})]
  				v86_boundedforall = v86_boundedforall && v88_in
  			}
  			if !(v86_boundedforall) {
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
  	v89_setliteral := map[string]any{}
  	if !(reflect.DeepEqual(this.state.msgs, v89_setliteral)) {
  		return fail("postcondition failed at %d; '(msgs) = {} (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed at %d; UNCHANGED(<<rmState>>) (prev: %+v, this: %+v)", trace_i, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckPReset(trace_i int, prev Event, this Event) error {
  
  	v90_setlit := map[string]any{}
  	v90_setlit[hash("r1")] = "r1"
  	v90_setlit[hash("r2")] = "r2"
  	v91_boundedforall := true
  	for v92, _ := range v90_setlit {
  		v90_setlit := map[string]any{}
  		v90_setlit[hash("r1")] = "r1"
  		v90_setlit[hash("r2")] = "r2"
  		v91_boundedforall = v91_boundedforall && reflect.DeepEqual(any(prev.state.rmState).(record)[any(v92).(string)], "aborted")
  	}
  	if !(v91_boundedforall) {
  
  		v93_setlit := map[string]any{}
  		v93_setlit[hash("r1")] = "r1"
  		v93_setlit[hash("r2")] = "r2"
  		v94_boundedforall := true
  		for v95, _ := range v93_setlit {
  			v93_setlit := map[string]any{}
  			v93_setlit[hash("r1")] = "r1"
  			v93_setlit[hash("r2")] = "r2"
  			v94_boundedforall = v94_boundedforall && reflect.DeepEqual(any(prev.state.rmState).(record)[any(v95).(string)], "committed")
  		}
  		if !(v94_boundedforall) {
  
  			v93_setlit := map[string]any{}
  			v93_setlit[hash("r1")] = "r1"
  			v93_setlit[hash("r2")] = "r2"
  			v94_boundedforall := true
  			for v95, _ := range v93_setlit {
  				v93_setlit := map[string]any{}
  				v93_setlit[hash("r1")] = "r1"
  				v93_setlit[hash("r2")] = "r2"
  				v94_boundedforall = v94_boundedforall && reflect.DeepEqual(any(prev.state.rmState).(record)[any(v95).(string)], "committed")
  			}
  			if !(v94_boundedforall) {
  				return fail("precondition failed at %d; (\\A r \\in RM : rmState[r] = \"aborted\" \\/ \\A r \\in RM : rmState[r] = \"committed\") (prev: %+v, this: %+v)", trace_i, prev, this)
  			}
  		}
  
  	}
  
  	v99_setlit := map[string]any{}
  	v99_setlit[hash("r1")] = "r1"
  	v99_setlit[hash("r2")] = "r2"
  	v96_fnconstr := map[any]any{}
  	for v97, _ := range v99_setlit {
  		v96_fnconstr[v97] = "working"
  	}
  
  	if !(reflect.DeepEqual(this.state.rmState, v96_fnconstr)) {
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
