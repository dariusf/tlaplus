
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
  
  type Monitor struct {
  	// the goal of extra is just to remove maintaining our own aux state,
  	// which may be annoying and error-prone as it may be passed across several functions
  	extra  []Event
  	events []Event
  }
  
  func New() Monitor {
  	return Monitor{
  		extra:  []Event{},
  		events: []Event{},
  	}
  }
  
  // TODO check initial
  
  func (m *Monitor) CheckTrace() error {
  	var prev Event
  	for i, this := range m.events {
  		if i == 0 {
  			prev = this
  			continue
  		}
  		switch this.typ {
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
  
  // CheckA
  func (m *Monitor) CheckA(trace_i int, prev Event, this Event) error {
  
  	if !(reflect.DeepEqual(this.state.x, prev.state.x.(int)+1)) {
  		return fail("postcondition failed at %d; expected reflect.DeepEqual(this.state.x, prev.state.x.(int) + 1) but got %s (prev: %+v, this: %+v)", trace_i, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  // CheckConstr
  func (m *Monitor) CheckConstr(trace_i int, prev Event, this Event) error {
  
  	if !(prev.state.x.(int) < 2) {
  		return fail("precondition failed at %d; expected prev.state.x.(int) < 2 but got %s (prev: %+v, this: %+v)", trace_i, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  // CheckInv
  func (m *Monitor) CheckInv(trace_i int, prev Event, this Event) error {
  
  	if !(prev.state.x.(int) < 3) {
  		return fail("precondition failed at %d; expected prev.state.x.(int) < 3 but got %s (prev: %+v, this: %+v)", trace_i, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  // translated straightforwardly from TLA+ action.
  // conjunctions become seq composition
  // disjunctions are all checked and at least one branch has to be true
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
  
  // can output a monitoring trace to show what happened from the perspective of the impl
  // this is also used to check certain things like post after pre
  // contribution is a scheme for producing monitors. checks only safety but TLA very expressive, some unique challenges there, just like apalache, which is otherwise routine. practical contribution
  // work on real raft
  // how to identify what the actions are? annotations or an extra variable in the ast that we can look at
  // types. or maybe cast on demand
  // minimize amount of engineering work, as markus said
  
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
  	D
  	E
  	F
  )
  
  func (e EventType) String() string {
  	switch e {
  	case A:
  		return "A"
  	case A1:
  		return "A1"
  	case B:
  		return "B"
  	case D:
  		return "D"
  	case E:
  		return "E"
  	case F:
  		return "F"
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
  
  type Monitor struct {
  	// the goal of extra is just to remove maintaining our own aux state,
  	// which may be annoying and error-prone as it may be passed across several functions
  	extra  []Event
  	events []Event
  }
  
  func New() Monitor {
  	return Monitor{
  		extra:  []Event{},
  		events: []Event{},
  	}
  }
  
  // TODO check initial
  
  func (m *Monitor) CheckTrace() error {
  	var prev Event
  	for i, this := range m.events {
  		if i == 0 {
  			prev = this
  			continue
  		}
  		switch this.typ {
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
  
  // CheckA
  func (m *Monitor) CheckA(trace_i int, prev Event, this Event) error {
  
  	if !(prev.state.x.(int) < 0) {
  		return fail("precondition failed at %d; expected prev.state.x.(int) < 0 but got %s (prev: %+v, this: %+v)", trace_i, prev.state.x, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.x, prev.state.x.(int)+1)) {
  		return fail("postcondition failed at %d; expected reflect.DeepEqual(this.state.x, prev.state.x.(int) + 1) but got %s (prev: %+v, this: %+v)", trace_i, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  // CheckA1
  func (m *Monitor) CheckA1(trace_i int, prev Event, this Event) error {
  
  	if !(prev.state.x.(int) < 0) {
  		return fail("precondition failed at %d; expected prev.state.x.(int) < 0 but got %s (prev: %+v, this: %+v)", trace_i, prev.state.x, prev, this)
  	}
  	if !(reflect.DeepEqual(this.state.x, prev.state.x.(int)+1) && prev.state.x.(int) < 0) {
  		return fail("precondition failed at %d; expected (reflect.DeepEqual(this.state.x, prev.state.x.(int) + 1) && prev.state.x.(int) < 0) but got %s (prev: %+v, this: %+v)", trace_i, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  // CheckB
  func (m *Monitor) CheckB(trace_i int, prev Event, this Event) error {
  
  	if !(reflect.DeepEqual(this.state.x, prev.state.x)) {
  		return fail("precondition failed at %d; expected reflect.DeepEqual(this.state.x, prev.state.x) but got %s (prev: %+v, this: %+v)", trace_i, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  // CheckD
  func (m *Monitor) CheckD(trace_i int, prev Event, this Event) error {
  
  	if !(reflect.DeepEqual(prev.state.x, 1) && reflect.DeepEqual(this.state.x, 2)) {
  
  		if !(!reflect.DeepEqual(prev.state.x, 1) && reflect.DeepEqual(this.state.x, 3)) {
  
  			if !(!reflect.DeepEqual(prev.state.x, 1) && reflect.DeepEqual(this.state.x, 3)) {
  				return fail("precondition failed at %d; expected (!reflect.DeepEqual(prev.state.x, 1) && reflect.DeepEqual(this.state.x, 3)) but got %s (prev: %+v, this: %+v)", trace_i, prev.state.x, prev, this)
  			}
  		}
  
  	}
  
  	return nil
  }
  
  // CheckE
  func (m *Monitor) CheckE(trace_i int, prev Event, this Event) error {
  
  	if !((reflect.DeepEqual(prev.state.x, 1) && reflect.DeepEqual(this.state.x, 2)) && (reflect.DeepEqual(prev.state.x, 2) || (reflect.DeepEqual(prev.state.x, 3) && reflect.DeepEqual(prev.state.x, 1)))) {
  
  		if !(!reflect.DeepEqual(prev.state.x, 1) && reflect.DeepEqual(this.state.x, 3)) {
  
  			if !(!reflect.DeepEqual(prev.state.x, 1) && reflect.DeepEqual(this.state.x, 3)) {
  				return fail("precondition failed at %d; expected (!reflect.DeepEqual(prev.state.x, 1) && reflect.DeepEqual(this.state.x, 3)) but got %s (prev: %+v, this: %+v)", trace_i, prev.state.x, prev, this)
  			}
  		}
  
  	}
  
  	return nil
  }
  
  // CheckF
  func (m *Monitor) CheckF(z any, trace_i int, prev Event, this Event) error {
  
  	if !(true) {
  		return fail("precondition failed at %d; expected true but got %s (prev: %+v, this: %+v)", trace_i, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  // translated straightforwardly from TLA+ action.
  // conjunctions become seq composition
  // disjunctions are all checked and at least one branch has to be true
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
  
  // can output a monitoring trace to show what happened from the perspective of the impl
  // this is also used to check certain things like post after pre
  // contribution is a scheme for producing monitors. checks only safety but TLA very expressive, some unique challenges there, just like apalache, which is otherwise routine. practical contribution
  // work on real raft
  // how to identify what the actions are? annotations or an extra variable in the ast that we can look at
  // types. or maybe cast on demand
  // minimize amount of engineering work, as markus said
  
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
  
  type Monitor struct {
  	// the goal of extra is just to remove maintaining our own aux state,
  	// which may be annoying and error-prone as it may be passed across several functions
  	extra  []Event
  	events []Event
  }
  
  func New() Monitor {
  	return Monitor{
  		extra:  []Event{},
  		events: []Event{},
  	}
  }
  
  // TODO check initial
  
  func (m *Monitor) CheckTrace() error {
  	var prev Event
  	for i, this := range m.events {
  		if i == 0 {
  			prev = this
  			continue
  		}
  		switch this.typ {
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
  
  // CheckA
  func (m *Monitor) CheckA(trace_i int, prev Event, this Event) error {
  
  	if !(reflect.DeepEqual(this.state.x, prev.state.x.(int)+1)) {
  		return fail("postcondition failed at %d; expected reflect.DeepEqual(this.state.x, prev.state.x.(int) + 1) but got %s (prev: %+v, this: %+v)", trace_i, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  // CheckConstr
  func (m *Monitor) CheckConstr(trace_i int, prev Event, this Event) error {
  
  	if !(prev.state.x.(int) < 2) {
  		return fail("precondition failed at %d; expected prev.state.x.(int) < 2 but got %s (prev: %+v, this: %+v)", trace_i, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  // CheckInv
  func (m *Monitor) CheckInv(trace_i int, prev Event, this Event) error {
  
  	if !(prev.state.x.(int) < 3) {
  		return fail("precondition failed at %d; expected prev.state.x.(int) < 3 but got %s (prev: %+v, this: %+v)", trace_i, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  // translated straightforwardly from TLA+ action.
  // conjunctions become seq composition
  // disjunctions are all checked and at least one branch has to be true
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
  
  // can output a monitoring trace to show what happened from the perspective of the impl
  // this is also used to check certain things like post after pre
  // contribution is a scheme for producing monitors. checks only safety but TLA very expressive, some unique challenges there, just like apalache, which is otherwise routine. practical contribution
  // work on real raft
  // how to identify what the actions are? annotations or an extra variable in the ast that we can look at
  // types. or maybe cast on demand
  // minimize amount of engineering work, as markus said
  
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
  TwoPhaseCommitFull.go:1:1: expected 'package', found 'EOF'
  TwoPhaseCommitFull.go:1:1: expected 'package', found 'EOF'
