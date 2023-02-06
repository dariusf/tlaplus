
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
  	"strconv"
  	"strings"
  )
  
  // TLA expressions
  type TLA interface {
  	String() string
  }
  
  type Seq struct {
  	elements []TLA
  }
  
  func (s Seq) String() string {
  	ss := []string{}
  	for _, v := range s.elements {
  		ss = append(ss, v.String())
  	}
  	return fmt.Sprintf("<<%s>>", strings.Join(ss, ", "))
  }
  
  type Record struct {
  	elements map[string]TLA
  }
  
  func (s Record) String() string {
  	ss := []string{}
  	for k, v := range s.elements {
  		ss = append(ss, fmt.Sprintf("%s |-> %s", k, v.String()))
  	}
  	return fmt.Sprintf("[%s]", strings.Join(ss, ", "))
  }
  
  type Set struct {
  	elements map[string]TLA
  }
  
  func (s Set) String() string {
  	ss := []string{}
  	for _, v := range s.elements {
  		ss = append(ss, v.String())
  	}
  	return fmt.Sprintf("{%s}", strings.Join(ss, ", "))
  }
  
  type Int struct {
  	value int
  }
  
  func (s Int) String() string {
  	return fmt.Sprintf("%d", s.value)
  }
  
  type Bool struct {
  	value bool
  }
  
  func (b Bool) String() string {
  	return strconv.FormatBool(b.value)
  }
  
  type String struct {
  	value string
  }
  
  func (s String) String() string {
  	return s.value
  }
  
  // smart constructors
  
  func boolean(b bool) Bool {
  	return Bool{value: b}
  }
  
  func integer(n int) Int {
  	return Int{value: n}
  }
  
  func str(s string) String {
  	return String{value: s}
  }
  
  func set(elts ...TLA) Set {
  	res := map[string]TLA{}
  	for _, v := range elts {
  		res[hash(v)] = v
  	}
  	return Set{elements: res}
  }
  
  func record(kvs ...TLA) Record {
  	res := map[string]TLA{}
  	for i := 0; i < len(kvs)/2; i += 2 {
  		res[kvs[i].(String).value] = kvs[i+1]
  	}
  	return Record{elements: res}
  }
  
  func seq(elts ...TLA) Seq {
  	return Seq{elements: elts}
  }
  
  // library
  
  func Some(a TLA) Seq {
  	return seq(a)
  }
  
  func None() Seq {
  	return seq()
  }
  
  func Append(a Seq, b Seq) Seq {
  	return Seq{elements: append(a.elements, b.elements...)}
  }
  
  func SetUnion(a Set, b Set) Set {
  	res := map[string]TLA{}
  	for k, v := range a.elements {
  		res[k] = v
  	}
  	for k, v := range b.elements {
  		res[k] = v
  	}
  	return Set{elements: res}
  }
  
  func SetIn(a TLA, b Set) Bool {
  	_, ok := b.elements[hash(a)]
  	return boolean(ok)
  }
  
  func SetNotIn(a TLA, b Set) Bool {
  	return boolean(!SetIn(a, b).value)
  }
  
  func RecordIndex(a Record, b String) TLA {
  	return a.elements[b.value]
  }
  
  func IntPlus(a Int, b Int) Int {
  	return integer(a.value + b.value)
  }
  
  func IntMinus(a Int, b Int) Int {
  	return integer(a.value - b.value)
  }
  
  func IntMul(a Int, b Int) Int {
  	return Int{value: a.value * b.value}
  }
  
  func IntLt(a Int, b Int) Bool {
  	return boolean(a.value < b.value)
  }
  
  func IntLte(a Int, b Int) Bool {
  	return boolean(a.value <= b.value)
  }
  
  func IntGt(a Int, b Int) Bool {
  	return boolean(a.value > b.value)
  }
  
  func IntGte(a Int, b Int) Bool {
  	return boolean(a.value >= b.value)
  }
  
  func Eq(a TLA, b TLA) Bool {
  	return boolean(reflect.DeepEqual(a, b))
  }
  
  func Not(b Bool) Bool {
  	return boolean(!b.value)
  }
  
  func Neq(a TLA, b TLA) Bool {
  	return Not(Eq(a, b))
  }
  
  func And(a Bool, b Bool) Bool {
  	return boolean(a.value && b.value)
  }
  
  func Or(a Bool, b Bool) Bool {
  	return boolean(a.value || b.value)
  }
  
  func IsFalse(a TLA) bool {
  	return !a.(Bool).value
  }
  
  func IsTrue(a TLA) bool {
  	return !IsFalse(a)
  }
  
  func ToSet(s Seq) Set {
  	res := map[string]TLA{}
  	for _, v := range s.elements {
  		res[hash(v)] = v
  	}
  	return Set{elements: res}
  }
  
  func Except(r Record, k String, v TLA) Record {
  	res := map[string]TLA{}
  	for k1, v1 := range r.elements {
  		res[k1] = v1
  	}
  	res[k.value] = v
  	return Record{elements: res}
  }
  
  func BoundedForall(set Set, f func(TLA) Bool) Bool {
  	res := true
  	for _, v := range set.elements {
  		res = true && IsTrue(f(v))
  	}
  	return Bool{value: res}
  }
  
  func FnConstruct(set Set, f func(TLA) TLA) Record {
  	res := map[string]TLA{}
  	for _, v := range set.elements {
  		res[v.(String).value] = f(v)
  	}
  	return Record{elements: res}
  }
  
  // panic instead of returning error
  var crash = true
  
  // this doesn't work for maps with non-string keys
  func hashjson(a any) string {
  	s, _ := json.Marshal(a)
  	return string(s)
  }
  
  func hash(a any) string {
  	return fmt.Sprintf("%+v", a)
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
  	x TLA
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
  	params []TLA
  	state  State
  	file   string
  	line   int
  }
  
  func printParams(ps []TLA) string {
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
  
  	if IsFalse(Eq(this.state.x, integer(1))) {
  		return fail("precondition failed in initial at %d; x = 1\n\nlhs: this.state.x = %+v\nrhs: integer(1) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.x, integer(1), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckA(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(Eq(this.state.x, IntPlus(prev.state.x.(Int), integer(1)))) {
  		return fail("postcondition failed in A at %d; '(x) = x + 1\n\nlhs: this.state.x = %+v\nrhs: IntPlus(prev.state.x.(Int), integer(1)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.x, IntPlus(prev.state.x.(Int), integer(1)), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckConstr(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(IntLt(prev.state.x.(Int), integer(2))) {
  		return fail("precondition failed in Constr at %d; x < 2\n\nlhs: prev.state.x.(Int) = %+v\nrhs: integer(2) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, prev.state.x.(Int), integer(2), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckInv(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(IntLt(prev.state.x.(Int), integer(3))) {
  		return fail("precondition failed in Inv at %d; x < 3\n\nlhs: prev.state.x.(Int) = %+v\nrhs: integer(3) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, prev.state.x.(Int), integer(3), prev, this)
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
  func (m *Monitor) CaptureVariable(v State, typ EventType, args ...TLA) error {
  
  	e := Event{
  		typ:    typ,
  		params: args,
  		state:  v,
  		// no need to capture file and line here
  	}
  	m.extra = append(m.extra, e)
  	return nil
  }
  
  func (m *Monitor) CaptureState(c State, typ EventType, args ...TLA) error {
  
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
  	"strconv"
  	"strings"
  )
  
  // TLA expressions
  type TLA interface {
  	String() string
  }
  
  type Seq struct {
  	elements []TLA
  }
  
  func (s Seq) String() string {
  	ss := []string{}
  	for _, v := range s.elements {
  		ss = append(ss, v.String())
  	}
  	return fmt.Sprintf("<<%s>>", strings.Join(ss, ", "))
  }
  
  type Record struct {
  	elements map[string]TLA
  }
  
  func (s Record) String() string {
  	ss := []string{}
  	for k, v := range s.elements {
  		ss = append(ss, fmt.Sprintf("%s |-> %s", k, v.String()))
  	}
  	return fmt.Sprintf("[%s]", strings.Join(ss, ", "))
  }
  
  type Set struct {
  	elements map[string]TLA
  }
  
  func (s Set) String() string {
  	ss := []string{}
  	for _, v := range s.elements {
  		ss = append(ss, v.String())
  	}
  	return fmt.Sprintf("{%s}", strings.Join(ss, ", "))
  }
  
  type Int struct {
  	value int
  }
  
  func (s Int) String() string {
  	return fmt.Sprintf("%d", s.value)
  }
  
  type Bool struct {
  	value bool
  }
  
  func (b Bool) String() string {
  	return strconv.FormatBool(b.value)
  }
  
  type String struct {
  	value string
  }
  
  func (s String) String() string {
  	return s.value
  }
  
  // smart constructors
  
  func boolean(b bool) Bool {
  	return Bool{value: b}
  }
  
  func integer(n int) Int {
  	return Int{value: n}
  }
  
  func str(s string) String {
  	return String{value: s}
  }
  
  func set(elts ...TLA) Set {
  	res := map[string]TLA{}
  	for _, v := range elts {
  		res[hash(v)] = v
  	}
  	return Set{elements: res}
  }
  
  func record(kvs ...TLA) Record {
  	res := map[string]TLA{}
  	for i := 0; i < len(kvs)/2; i += 2 {
  		res[kvs[i].(String).value] = kvs[i+1]
  	}
  	return Record{elements: res}
  }
  
  func seq(elts ...TLA) Seq {
  	return Seq{elements: elts}
  }
  
  // library
  
  func Some(a TLA) Seq {
  	return seq(a)
  }
  
  func None() Seq {
  	return seq()
  }
  
  func Append(a Seq, b Seq) Seq {
  	return Seq{elements: append(a.elements, b.elements...)}
  }
  
  func SetUnion(a Set, b Set) Set {
  	res := map[string]TLA{}
  	for k, v := range a.elements {
  		res[k] = v
  	}
  	for k, v := range b.elements {
  		res[k] = v
  	}
  	return Set{elements: res}
  }
  
  func SetIn(a TLA, b Set) Bool {
  	_, ok := b.elements[hash(a)]
  	return boolean(ok)
  }
  
  func SetNotIn(a TLA, b Set) Bool {
  	return boolean(!SetIn(a, b).value)
  }
  
  func RecordIndex(a Record, b String) TLA {
  	return a.elements[b.value]
  }
  
  func IntPlus(a Int, b Int) Int {
  	return integer(a.value + b.value)
  }
  
  func IntMinus(a Int, b Int) Int {
  	return integer(a.value - b.value)
  }
  
  func IntMul(a Int, b Int) Int {
  	return Int{value: a.value * b.value}
  }
  
  func IntLt(a Int, b Int) Bool {
  	return boolean(a.value < b.value)
  }
  
  func IntLte(a Int, b Int) Bool {
  	return boolean(a.value <= b.value)
  }
  
  func IntGt(a Int, b Int) Bool {
  	return boolean(a.value > b.value)
  }
  
  func IntGte(a Int, b Int) Bool {
  	return boolean(a.value >= b.value)
  }
  
  func Eq(a TLA, b TLA) Bool {
  	return boolean(reflect.DeepEqual(a, b))
  }
  
  func Not(b Bool) Bool {
  	return boolean(!b.value)
  }
  
  func Neq(a TLA, b TLA) Bool {
  	return Not(Eq(a, b))
  }
  
  func And(a Bool, b Bool) Bool {
  	return boolean(a.value && b.value)
  }
  
  func Or(a Bool, b Bool) Bool {
  	return boolean(a.value || b.value)
  }
  
  func IsFalse(a TLA) bool {
  	return !a.(Bool).value
  }
  
  func IsTrue(a TLA) bool {
  	return !IsFalse(a)
  }
  
  func ToSet(s Seq) Set {
  	res := map[string]TLA{}
  	for _, v := range s.elements {
  		res[hash(v)] = v
  	}
  	return Set{elements: res}
  }
  
  func Except(r Record, k String, v TLA) Record {
  	res := map[string]TLA{}
  	for k1, v1 := range r.elements {
  		res[k1] = v1
  	}
  	res[k.value] = v
  	return Record{elements: res}
  }
  
  func BoundedForall(set Set, f func(TLA) Bool) Bool {
  	res := true
  	for _, v := range set.elements {
  		res = true && IsTrue(f(v))
  	}
  	return Bool{value: res}
  }
  
  func FnConstruct(set Set, f func(TLA) TLA) Record {
  	res := map[string]TLA{}
  	for _, v := range set.elements {
  		res[v.(String).value] = f(v)
  	}
  	return Record{elements: res}
  }
  
  // panic instead of returning error
  var crash = true
  
  // this doesn't work for maps with non-string keys
  func hashjson(a any) string {
  	s, _ := json.Marshal(a)
  	return string(s)
  }
  
  func hash(a any) string {
  	return fmt.Sprintf("%+v", a)
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
  	x TLA
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
  	H4
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
  	case H4:
  		return "H4"
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
  	params []TLA
  	state  State
  	file   string
  	line   int
  }
  
  func printParams(ps []TLA) string {
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
  		case H4:
  			if err := m.CheckH4(i, prev, this); err != nil {
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
  
  	if IsFalse(Eq(this.state.x, integer(1))) {
  		return fail("precondition failed in initial at %d; x = 1\n\nlhs: this.state.x = %+v\nrhs: integer(1) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.x, integer(1), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckA(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(IntLt(prev.state.x.(Int), integer(0))) {
  		return fail("precondition failed in A at %d; x < 0\n\nlhs: prev.state.x.(Int) = %+v\nrhs: integer(0) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, prev.state.x.(Int), integer(0), prev, this)
  	}
  	if IsFalse(Eq(this.state.x, IntPlus(prev.state.x.(Int), integer(1)))) {
  		return fail("postcondition failed in A at %d; '(x) = x + 1\n\nlhs: this.state.x = %+v\nrhs: IntPlus(prev.state.x.(Int), integer(1)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.x, IntPlus(prev.state.x.(Int), integer(1)), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckA1(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(IntLt(prev.state.x.(Int), integer(0))) {
  		return fail("precondition failed in A1 at %d; x < 0\n\nlhs: prev.state.x.(Int) = %+v\nrhs: integer(0) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, prev.state.x.(Int), integer(0), prev, this)
  	}
  	if IsFalse(And(Eq(this.state.x, IntPlus(prev.state.x.(Int), integer(1))), IntLt(prev.state.x.(Int), integer(0)))) {
  		return fail("precondition failed in A1 at %d; '(x) = x + 1 \\land x < 0\n\nlhs: Eq(this.state.x, IntPlus(prev.state.x.(Int), integer(1))) = %+v\nrhs: IntLt(prev.state.x.(Int), integer(0)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, Eq(this.state.x, IntPlus(prev.state.x.(Int), integer(1))), IntLt(prev.state.x.(Int), integer(0)), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckB(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(Eq(this.state.x, prev.state.x)) {
  		return fail("precondition failed in B at %d; UNCHANGED(x)\n\nlhs: this.state.x = %+v\nrhs: prev.state.x = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.x, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckC(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(Eq(prev.state.x, prev.state.x)) {
  		return fail("precondition failed in C at %d; Send(x)\n\nlhs: prev.state.x = %+v\nrhs: prev.state.x = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, prev.state.x, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckD(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(And(Eq(prev.state.x, integer(1)), Eq(this.state.x, integer(2)))) {
  
  		if IsFalse(And(Neq(prev.state.x, integer(1)), Eq(this.state.x, integer(3)))) {
  			return fail("precondition failed in D at %d; ((x = 1 /\\ '(x) = 2) \\/ (x /= 1 /\\ '(x) = 3))\n\nlhs: Neq(prev.state.x, integer(1)) = %+v\nrhs: Eq(this.state.x, integer(3)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, Neq(prev.state.x, integer(1)), Eq(this.state.x, integer(3)), prev, this)
  		}
  	}
  
  	return nil
  }
  
  func (m *Monitor) CheckE(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(And(And(Eq(prev.state.x, integer(1)), Eq(this.state.x, integer(2))), Or(Eq(prev.state.x, integer(2)), And(Eq(prev.state.x, integer(3)), Eq(prev.state.x, integer(1)))))) {
  
  		if IsFalse(And(Neq(prev.state.x, integer(1)), Eq(this.state.x, integer(3)))) {
  			return fail("precondition failed in E at %d; ((x = 1 /\\ '(x) = 2) \\/ (x /= 1 /\\ '(x) = 3))\n\nlhs: Neq(prev.state.x, integer(1)) = %+v\nrhs: Eq(this.state.x, integer(3)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, Neq(prev.state.x, integer(1)), Eq(this.state.x, integer(3)), prev, this)
  		}
  	}
  
  	return nil
  }
  
  func (m *Monitor) CheckF(z TLA, trace_i int, prev Event, this Event) error {
  
  	if IsFalse(boolean(true)) {
  		return fail("precondition failed in F at %d; TRUE\n\nlhs: \"<none>\" = %+v\nrhs: \"<none>\" = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, "<none>", "<none>", prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckG(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(Eq(RecordIndex(Except(record(str("a"), integer(1)), str("a"), integer(2)), str("a")), integer(2))) {
  		return fail("precondition failed in G at %d; [[\"a\" |-> 1] EXCEPT ![\"a\"] = 2][\"a\"] = 2\n\nlhs: RecordIndex(Except(record(str(\"a\"), integer(1)), str(\"a\"), integer(2)), str(\"a\")) = %+v\nrhs: integer(2) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, RecordIndex(Except(record(str("a"), integer(1)), str("a"), integer(2)), str("a")), integer(2), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckH(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(BoundedForall(set(integer(1), integer(2)), func(v0 TLA) Bool { return Eq(v0, integer(1)) })) {
  		return fail("precondition failed in H at %d; \\A r \\in {1, 2} : r = 1\n\nlhs: set(integer(1), integer(2)) = %+v\nrhs: \"<func>\" = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, set(integer(1), integer(2)), "<func>", prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckH1(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(BoundedForall(set(integer(1), integer(2)), func(v1 TLA) Bool {
  		return BoundedForall(set(integer(3), integer(4)), func(v2 TLA) Bool { return Eq(v2, v1) })
  	})) {
  		return fail("precondition failed in H1 at %d; \\A s \\in {1, 2} : \\A r \\in {3, 4} : r = s\n\nlhs: set(integer(1), integer(2)) = %+v\nrhs: \"<func>\" = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, set(integer(1), integer(2)), "<func>", prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckH2(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(Eq(RecordIndex(FnConstruct(set(str("s1"), str("2")), func(_ TLA) TLA { return str("a") }), str("a")), integer(1))) {
  		return fail("precondition failed in H2 at %d; [ r \\in RM |-> \"a\" ][\"a\"] = 1\n\nlhs: RecordIndex(FnConstruct(set(str(\"s1\"), str(\"2\")), func(_ TLA) TLA { return str(\"a\") }), str(\"a\")) = %+v\nrhs: integer(1) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, RecordIndex(FnConstruct(set(str("s1"), str("2")), func(_ TLA) TLA { return str("a") }), str("a")), integer(1), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckH3(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(Eq(RecordIndex(FnConstruct(set(str("s1"), str("2")), func(v4 TLA) TLA { return v4.(Set) }), str("a")), integer(1))) {
  		return fail("precondition failed in H3 at %d; [ r \\in RM |-> r ][\"a\"] = 1\n\nlhs: RecordIndex(FnConstruct(set(str(\"s1\"), str(\"2\")), func(v4 TLA) TLA { return v4.(Set) }), str(\"a\")) = %+v\nrhs: integer(1) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, RecordIndex(FnConstruct(set(str("s1"), str("2")), func(v4 TLA) TLA { return v4.(Set) }), str("a")), integer(1), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckH4(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(BoundedForall(set(integer(1), integer(2)), func(v5 TLA) Bool { return Eq(v5, integer(1)) })) {
  
  		if IsFalse(BoundedForall(set(integer(2), integer(3)), func(v6 TLA) Bool { return Eq(v6, integer(2)) })) {
  			return fail("precondition failed in H4 at %d; (\\A r \\in {1, 2} : r = 1 \\/ \\A r \\in {2, 3} : r = 2)\n\nlhs: set(integer(2), integer(3)) = %+v\nrhs: \"<func>\" = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, set(integer(2), integer(3)), "<func>", prev, this)
  		}
  	}
  
  	return nil
  }
  
  /* Action I cannot be translated because of: ToTrace(CounterExample) */
  
  /* Action a cannot be translated because of: a is not an OpApplNode but an NumeralNode */
  
  /* Action b cannot be translated because of: b is not an OpApplNode but an NumeralNode */
  
  /* Action c cannot be translated because of: c is not an OpApplNode but an NumeralNode */
  
  func (m *Monitor) CheckI1(trace_i int, prev Event, this Event) error {
  
  	var a TLA = integer(1)
  	var b TLA = integer(1)
  	var c TLA = integer(1)
  	if IsFalse(Eq(IntPlus(IntPlus(a.(Int), b.(Int)), c.(Int)), integer(1))) {
  		return fail("precondition failed in I1 at %d; a + b + c = 1\n\nlhs: IntPlus(IntPlus(a.(Int), b.(Int)), c.(Int)) = %+v\nrhs: integer(1) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, IntPlus(IntPlus(a.(Int), b.(Int)), c.(Int)), integer(1), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckSets(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(Eq(SetUnion(set(integer(1), integer(2)), set(integer(3))), set())) {
  		return fail("precondition failed in Sets at %d; {1, 2} \\union {3} = {}\n\nlhs: SetUnion(set(integer(1), integer(2)), set(integer(3))) = %+v\nrhs: set() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, SetUnion(set(integer(1), integer(2)), set(integer(3))), set(), prev, this)
  	}
  	if IsFalse(SetNotIn(integer(1), set(integer(3)))) {
  		return fail("precondition failed in Sets at %d; 1 \\notin {3}\n\nlhs: integer(1) = %+v\nrhs: set(integer(3)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, integer(1), set(integer(3)), prev, this)
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
  func (m *Monitor) CaptureVariable(v State, typ EventType, args ...TLA) error {
  
  	e := Event{
  		typ:    typ,
  		params: args,
  		state:  v,
  		// no need to capture file and line here
  	}
  	m.extra = append(m.extra, e)
  	return nil
  }
  
  func (m *Monitor) CaptureState(c State, typ EventType, args ...TLA) error {
  
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
  	"strconv"
  	"strings"
  )
  
  // TLA expressions
  type TLA interface {
  	String() string
  }
  
  type Seq struct {
  	elements []TLA
  }
  
  func (s Seq) String() string {
  	ss := []string{}
  	for _, v := range s.elements {
  		ss = append(ss, v.String())
  	}
  	return fmt.Sprintf("<<%s>>", strings.Join(ss, ", "))
  }
  
  type Record struct {
  	elements map[string]TLA
  }
  
  func (s Record) String() string {
  	ss := []string{}
  	for k, v := range s.elements {
  		ss = append(ss, fmt.Sprintf("%s |-> %s", k, v.String()))
  	}
  	return fmt.Sprintf("[%s]", strings.Join(ss, ", "))
  }
  
  type Set struct {
  	elements map[string]TLA
  }
  
  func (s Set) String() string {
  	ss := []string{}
  	for _, v := range s.elements {
  		ss = append(ss, v.String())
  	}
  	return fmt.Sprintf("{%s}", strings.Join(ss, ", "))
  }
  
  type Int struct {
  	value int
  }
  
  func (s Int) String() string {
  	return fmt.Sprintf("%d", s.value)
  }
  
  type Bool struct {
  	value bool
  }
  
  func (b Bool) String() string {
  	return strconv.FormatBool(b.value)
  }
  
  type String struct {
  	value string
  }
  
  func (s String) String() string {
  	return s.value
  }
  
  // smart constructors
  
  func boolean(b bool) Bool {
  	return Bool{value: b}
  }
  
  func integer(n int) Int {
  	return Int{value: n}
  }
  
  func str(s string) String {
  	return String{value: s}
  }
  
  func set(elts ...TLA) Set {
  	res := map[string]TLA{}
  	for _, v := range elts {
  		res[hash(v)] = v
  	}
  	return Set{elements: res}
  }
  
  func record(kvs ...TLA) Record {
  	res := map[string]TLA{}
  	for i := 0; i < len(kvs)/2; i += 2 {
  		res[kvs[i].(String).value] = kvs[i+1]
  	}
  	return Record{elements: res}
  }
  
  func seq(elts ...TLA) Seq {
  	return Seq{elements: elts}
  }
  
  // library
  
  func Some(a TLA) Seq {
  	return seq(a)
  }
  
  func None() Seq {
  	return seq()
  }
  
  func Append(a Seq, b Seq) Seq {
  	return Seq{elements: append(a.elements, b.elements...)}
  }
  
  func SetUnion(a Set, b Set) Set {
  	res := map[string]TLA{}
  	for k, v := range a.elements {
  		res[k] = v
  	}
  	for k, v := range b.elements {
  		res[k] = v
  	}
  	return Set{elements: res}
  }
  
  func SetIn(a TLA, b Set) Bool {
  	_, ok := b.elements[hash(a)]
  	return boolean(ok)
  }
  
  func SetNotIn(a TLA, b Set) Bool {
  	return boolean(!SetIn(a, b).value)
  }
  
  func RecordIndex(a Record, b String) TLA {
  	return a.elements[b.value]
  }
  
  func IntPlus(a Int, b Int) Int {
  	return integer(a.value + b.value)
  }
  
  func IntMinus(a Int, b Int) Int {
  	return integer(a.value - b.value)
  }
  
  func IntMul(a Int, b Int) Int {
  	return Int{value: a.value * b.value}
  }
  
  func IntLt(a Int, b Int) Bool {
  	return boolean(a.value < b.value)
  }
  
  func IntLte(a Int, b Int) Bool {
  	return boolean(a.value <= b.value)
  }
  
  func IntGt(a Int, b Int) Bool {
  	return boolean(a.value > b.value)
  }
  
  func IntGte(a Int, b Int) Bool {
  	return boolean(a.value >= b.value)
  }
  
  func Eq(a TLA, b TLA) Bool {
  	return boolean(reflect.DeepEqual(a, b))
  }
  
  func Not(b Bool) Bool {
  	return boolean(!b.value)
  }
  
  func Neq(a TLA, b TLA) Bool {
  	return Not(Eq(a, b))
  }
  
  func And(a Bool, b Bool) Bool {
  	return boolean(a.value && b.value)
  }
  
  func Or(a Bool, b Bool) Bool {
  	return boolean(a.value || b.value)
  }
  
  func IsFalse(a TLA) bool {
  	return !a.(Bool).value
  }
  
  func IsTrue(a TLA) bool {
  	return !IsFalse(a)
  }
  
  func ToSet(s Seq) Set {
  	res := map[string]TLA{}
  	for _, v := range s.elements {
  		res[hash(v)] = v
  	}
  	return Set{elements: res}
  }
  
  func Except(r Record, k String, v TLA) Record {
  	res := map[string]TLA{}
  	for k1, v1 := range r.elements {
  		res[k1] = v1
  	}
  	res[k.value] = v
  	return Record{elements: res}
  }
  
  func BoundedForall(set Set, f func(TLA) Bool) Bool {
  	res := true
  	for _, v := range set.elements {
  		res = true && IsTrue(f(v))
  	}
  	return Bool{value: res}
  }
  
  func FnConstruct(set Set, f func(TLA) TLA) Record {
  	res := map[string]TLA{}
  	for _, v := range set.elements {
  		res[v.(String).value] = f(v)
  	}
  	return Record{elements: res}
  }
  
  // panic instead of returning error
  var crash = true
  
  // this doesn't work for maps with non-string keys
  func hashjson(a any) string {
  	s, _ := json.Marshal(a)
  	return string(s)
  }
  
  func hash(a any) string {
  	return fmt.Sprintf("%+v", a)
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
  	x TLA
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
  	params []TLA
  	state  State
  	file   string
  	line   int
  }
  
  func printParams(ps []TLA) string {
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
  
  	if IsFalse(Eq(this.state.x, integer(1))) {
  		return fail("precondition failed in initial at %d; x = 1\n\nlhs: this.state.x = %+v\nrhs: integer(1) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.x, integer(1), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckA(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(Eq(this.state.x, IntPlus(prev.state.x.(Int), integer(1)))) {
  		return fail("postcondition failed in A at %d; '(x) = x + 1\n\nlhs: this.state.x = %+v\nrhs: IntPlus(prev.state.x.(Int), integer(1)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.x, IntPlus(prev.state.x.(Int), integer(1)), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckConstr(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(IntLt(prev.state.x.(Int), integer(2))) {
  		return fail("precondition failed in Constr at %d; x < 2\n\nlhs: prev.state.x.(Int) = %+v\nrhs: integer(2) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, prev.state.x.(Int), integer(2), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckInv(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(IntLt(prev.state.x.(Int), integer(3))) {
  		return fail("precondition failed in Inv at %d; x < 3\n\nlhs: prev.state.x.(Int) = %+v\nrhs: integer(3) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, prev.state.x.(Int), integer(3), prev, this)
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
  func (m *Monitor) CaptureVariable(v State, typ EventType, args ...TLA) error {
  
  	e := Event{
  		typ:    typ,
  		params: args,
  		state:  v,
  		// no need to capture file and line here
  	}
  	m.extra = append(m.extra, e)
  	return nil
  }
  
  func (m *Monitor) CaptureState(c State, typ EventType, args ...TLA) error {
  
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
  	"strconv"
  	"strings"
  )
  
  // TLA expressions
  type TLA interface {
  	String() string
  }
  
  type Seq struct {
  	elements []TLA
  }
  
  func (s Seq) String() string {
  	ss := []string{}
  	for _, v := range s.elements {
  		ss = append(ss, v.String())
  	}
  	return fmt.Sprintf("<<%s>>", strings.Join(ss, ", "))
  }
  
  type Record struct {
  	elements map[string]TLA
  }
  
  func (s Record) String() string {
  	ss := []string{}
  	for k, v := range s.elements {
  		ss = append(ss, fmt.Sprintf("%s |-> %s", k, v.String()))
  	}
  	return fmt.Sprintf("[%s]", strings.Join(ss, ", "))
  }
  
  type Set struct {
  	elements map[string]TLA
  }
  
  func (s Set) String() string {
  	ss := []string{}
  	for _, v := range s.elements {
  		ss = append(ss, v.String())
  	}
  	return fmt.Sprintf("{%s}", strings.Join(ss, ", "))
  }
  
  type Int struct {
  	value int
  }
  
  func (s Int) String() string {
  	return fmt.Sprintf("%d", s.value)
  }
  
  type Bool struct {
  	value bool
  }
  
  func (b Bool) String() string {
  	return strconv.FormatBool(b.value)
  }
  
  type String struct {
  	value string
  }
  
  func (s String) String() string {
  	return s.value
  }
  
  // smart constructors
  
  func boolean(b bool) Bool {
  	return Bool{value: b}
  }
  
  func integer(n int) Int {
  	return Int{value: n}
  }
  
  func str(s string) String {
  	return String{value: s}
  }
  
  func set(elts ...TLA) Set {
  	res := map[string]TLA{}
  	for _, v := range elts {
  		res[hash(v)] = v
  	}
  	return Set{elements: res}
  }
  
  func record(kvs ...TLA) Record {
  	res := map[string]TLA{}
  	for i := 0; i < len(kvs)/2; i += 2 {
  		res[kvs[i].(String).value] = kvs[i+1]
  	}
  	return Record{elements: res}
  }
  
  func seq(elts ...TLA) Seq {
  	return Seq{elements: elts}
  }
  
  // library
  
  func Some(a TLA) Seq {
  	return seq(a)
  }
  
  func None() Seq {
  	return seq()
  }
  
  func Append(a Seq, b Seq) Seq {
  	return Seq{elements: append(a.elements, b.elements...)}
  }
  
  func SetUnion(a Set, b Set) Set {
  	res := map[string]TLA{}
  	for k, v := range a.elements {
  		res[k] = v
  	}
  	for k, v := range b.elements {
  		res[k] = v
  	}
  	return Set{elements: res}
  }
  
  func SetIn(a TLA, b Set) Bool {
  	_, ok := b.elements[hash(a)]
  	return boolean(ok)
  }
  
  func SetNotIn(a TLA, b Set) Bool {
  	return boolean(!SetIn(a, b).value)
  }
  
  func RecordIndex(a Record, b String) TLA {
  	return a.elements[b.value]
  }
  
  func IntPlus(a Int, b Int) Int {
  	return integer(a.value + b.value)
  }
  
  func IntMinus(a Int, b Int) Int {
  	return integer(a.value - b.value)
  }
  
  func IntMul(a Int, b Int) Int {
  	return Int{value: a.value * b.value}
  }
  
  func IntLt(a Int, b Int) Bool {
  	return boolean(a.value < b.value)
  }
  
  func IntLte(a Int, b Int) Bool {
  	return boolean(a.value <= b.value)
  }
  
  func IntGt(a Int, b Int) Bool {
  	return boolean(a.value > b.value)
  }
  
  func IntGte(a Int, b Int) Bool {
  	return boolean(a.value >= b.value)
  }
  
  func Eq(a TLA, b TLA) Bool {
  	return boolean(reflect.DeepEqual(a, b))
  }
  
  func Not(b Bool) Bool {
  	return boolean(!b.value)
  }
  
  func Neq(a TLA, b TLA) Bool {
  	return Not(Eq(a, b))
  }
  
  func And(a Bool, b Bool) Bool {
  	return boolean(a.value && b.value)
  }
  
  func Or(a Bool, b Bool) Bool {
  	return boolean(a.value || b.value)
  }
  
  func IsFalse(a TLA) bool {
  	return !a.(Bool).value
  }
  
  func IsTrue(a TLA) bool {
  	return !IsFalse(a)
  }
  
  func ToSet(s Seq) Set {
  	res := map[string]TLA{}
  	for _, v := range s.elements {
  		res[hash(v)] = v
  	}
  	return Set{elements: res}
  }
  
  func Except(r Record, k String, v TLA) Record {
  	res := map[string]TLA{}
  	for k1, v1 := range r.elements {
  		res[k1] = v1
  	}
  	res[k.value] = v
  	return Record{elements: res}
  }
  
  func BoundedForall(set Set, f func(TLA) Bool) Bool {
  	res := true
  	for _, v := range set.elements {
  		res = true && IsTrue(f(v))
  	}
  	return Bool{value: res}
  }
  
  func FnConstruct(set Set, f func(TLA) TLA) Record {
  	res := map[string]TLA{}
  	for _, v := range set.elements {
  		res[v.(String).value] = f(v)
  	}
  	return Record{elements: res}
  }
  
  // panic instead of returning error
  var crash = true
  
  // this doesn't work for maps with non-string keys
  func hashjson(a any) string {
  	s, _ := json.Marshal(a)
  	return string(s)
  }
  
  func hash(a any) string {
  	return fmt.Sprintf("%+v", a)
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
  	who             TLA
  	lastMsgReceived TLA
  	tmCommitted     TLA
  	lastMsgSent     TLA
  	tmPrepared      TLA
  	msgs            TLA
  	tmAborted       TLA
  	rmState         TLA
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
  	params []TLA
  	state  State
  	file   string
  	line   int
  }
  
  func printParams(ps []TLA) string {
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
  
  	if IsFalse(Eq(this.state.msgs, set())) {
  		return fail("precondition failed in initial at %d; msgs = {}\n\nlhs: this.state.msgs = %+v\nrhs: set() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.msgs, set(), prev, this)
  	}
  	if IsFalse(Eq(this.state.tmAborted, seq())) {
  		return fail("precondition failed in initial at %d; tmAborted = <<>>\n\nlhs: this.state.tmAborted = %+v\nrhs: seq() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.tmAborted, seq(), prev, this)
  	}
  	if IsFalse(Eq(this.state.tmCommitted, seq())) {
  		return fail("precondition failed in initial at %d; tmCommitted = <<>>\n\nlhs: this.state.tmCommitted = %+v\nrhs: seq() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.tmCommitted, seq(), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgSent, seq())) {
  		return fail("precondition failed in initial at %d; lastMsgSent = <<>>\n\nlhs: this.state.lastMsgSent = %+v\nrhs: seq() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgSent, seq(), prev, this)
  	}
  	if IsFalse(Eq(this.state.tmPrepared, seq())) {
  		return fail("precondition failed in initial at %d; tmPrepared = <<>>\n\nlhs: this.state.tmPrepared = %+v\nrhs: seq() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.tmPrepared, seq(), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgReceived, seq())) {
  		return fail("precondition failed in initial at %d; lastMsgReceived = <<>>\n\nlhs: this.state.lastMsgReceived = %+v\nrhs: seq() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgReceived, seq(), prev, this)
  	}
  	if IsFalse(Eq(this.state.rmState, record(str("r1"), str("working"), str("r2"), str("working")))) {
  		return fail("precondition failed in initial at %d; rmState = [r1 |-> \"working\", r2 |-> \"working\"]\n\nlhs: this.state.rmState = %+v\nrhs: record(str(\"r1\"), str(\"working\"), str(\"r2\"), str(\"working\")) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.rmState, record(str("r1"), str("working"), str("r2"), str("working")), prev, this)
  	}
  	if IsFalse(Eq(this.state.who, str("none"))) {
  		return fail("precondition failed in initial at %d; who = \"none\"\n\nlhs: this.state.who = %+v\nrhs: str(\"none\") = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.who, str("none"), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCReceivePrepare(r TLA, trace_i int, prev Event, this Event) error {
  
  	if IsFalse(SetIn(record(str("type"), str("Prepared"), str("rm"), r), prev.state.msgs.(Set))) {
  		return fail("precondition failed in CReceivePrepare at %d; Receive([\"type\" |-> \"Prepared\", \"rm\" |-> r])\n\nlhs: record(str(\"type\"), str(\"Prepared\"), str(\"rm\"), r) = %+v\nrhs: prev.state.msgs.(Set) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, record(str("type"), str("Prepared"), str("rm"), r), prev.state.msgs.(Set), prev, this)
  	}
  	if IsFalse(SetNotIn(r, ToSet(prev.state.tmPrepared.(Seq)))) {
  		return fail("precondition failed in CReceivePrepare at %d; r \\notin ToSet(tmPrepared)\n\nlhs: r = %+v\nrhs: ToSet(prev.state.tmPrepared.(Seq)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, r, ToSet(prev.state.tmPrepared.(Seq)), prev, this)
  	}
  	if IsFalse(Eq(this.state.tmPrepared, Append(prev.state.tmPrepared.(Seq), r.(Seq)))) {
  		return fail("postcondition failed in CReceivePrepare at %d; '(tmPrepared) = Append(tmPrepared, r)\n\nlhs: this.state.tmPrepared = %+v\nrhs: Append(prev.state.tmPrepared.(Seq), r.(Seq)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.tmPrepared, Append(prev.state.tmPrepared.(Seq), r.(Seq)), prev, this)
  	}
  	if IsFalse(Eq(this.state.who, str("coordinator"))) {
  		return fail("postcondition failed in CReceivePrepare at %d; '(who) = \"coordinator\"\n\nlhs: this.state.who = %+v\nrhs: str(\"coordinator\") = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.who, str("coordinator"), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgReceived, Some(record(str("type"), str("Prepared"), str("rm"), r)))) {
  		return fail("postcondition failed in CReceivePrepare at %d; '(lastMsgReceived) = Some([\"type\" |-> \"Prepared\", \"rm\" |-> r])\n\nlhs: this.state.lastMsgReceived = %+v\nrhs: Some(record(str(\"type\"), str(\"Prepared\"), str(\"rm\"), r)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgReceived, Some(record(str("type"), str("Prepared"), str("rm"), r)), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgSent, None())) {
  		return fail("postcondition failed in CReceivePrepare at %d; '(lastMsgSent) = None\n\nlhs: this.state.lastMsgSent = %+v\nrhs: None() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgSent, None(), prev, this)
  	}
  	if IsFalse(Eq(this.state.msgs, prev.state.msgs)) {
  		return fail("precondition failed in CReceivePrepare at %d; UNCHANGED(<<msgs>>)\n\nlhs: this.state.msgs = %+v\nrhs: prev.state.msgs = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.msgs, prev.state.msgs, prev, this)
  	}
  	if IsFalse(Eq(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed in CReceivePrepare at %d; UNCHANGED(<<rmState>>)\n\nlhs: this.state.rmState = %+v\nrhs: prev.state.rmState = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.rmState, prev.state.rmState, prev, this)
  	}
  	if IsFalse(And(Eq(this.state.tmCommitted, prev.state.tmCommitted), Eq(this.state.tmAborted, prev.state.tmAborted))) {
  		return fail("precondition failed in CReceivePrepare at %d; UNCHANGED(<<tmCommitted, tmAborted>>)\n\nlhs: Eq(this.state.tmCommitted, prev.state.tmCommitted) = %+v\nrhs: Eq(this.state.tmAborted, prev.state.tmAborted) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, Eq(this.state.tmCommitted, prev.state.tmCommitted), Eq(this.state.tmAborted, prev.state.tmAborted), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCSendPrepare(r TLA, trace_i int, prev Event, this Event) error {
  
  	if IsFalse(Neq(ToSet(prev.state.tmPrepared.(Seq)), set(str("r1"), str("r2")))) {
  		return fail("precondition failed in CSendPrepare at %d; ToSet(tmPrepared) /= RM\n\nlhs: ToSet(prev.state.tmPrepared.(Seq)) = %+v\nrhs: set(str(\"r1\"), str(\"r2\")) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, ToSet(prev.state.tmPrepared.(Seq)), set(str("r1"), str("r2")), prev, this)
  	}
  	if IsFalse(And(SetNotIn(record(str("type"), str("Prepare"), str("rm"), r), prev.state.msgs.(Set)), Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str("type"), str("Prepare"), str("rm"), r)))))) {
  		return fail("precondition failed in CSendPrepare at %d; Send([\"type\" |-> \"Prepare\", \"rm\" |-> r])\n\nlhs: SetNotIn(record(str(\"type\"), str(\"Prepare\"), str(\"rm\"), r), prev.state.msgs.(Set)) = %+v\nrhs: Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str(\"type\"), str(\"Prepare\"), str(\"rm\"), r)))) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, SetNotIn(record(str("type"), str("Prepare"), str("rm"), r), prev.state.msgs.(Set)), Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str("type"), str("Prepare"), str("rm"), r)))), prev, this)
  	}
  	if IsFalse(Eq(this.state.who, str("coordinator"))) {
  		return fail("postcondition failed in CSendPrepare at %d; '(who) = \"coordinator\"\n\nlhs: this.state.who = %+v\nrhs: str(\"coordinator\") = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.who, str("coordinator"), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgReceived, None())) {
  		return fail("postcondition failed in CSendPrepare at %d; '(lastMsgReceived) = None\n\nlhs: this.state.lastMsgReceived = %+v\nrhs: None() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgReceived, None(), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgSent, Some(record(str("type"), str("Prepare"), str("rm"), r)))) {
  		return fail("postcondition failed in CSendPrepare at %d; '(lastMsgSent) = Some([\"type\" |-> \"Prepare\", \"rm\" |-> r])\n\nlhs: this.state.lastMsgSent = %+v\nrhs: Some(record(str(\"type\"), str(\"Prepare\"), str(\"rm\"), r)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgSent, Some(record(str("type"), str("Prepare"), str("rm"), r)), prev, this)
  	}
  	if IsFalse(Eq(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed in CSendPrepare at %d; UNCHANGED(<<rmState>>)\n\nlhs: this.state.rmState = %+v\nrhs: prev.state.rmState = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.rmState, prev.state.rmState, prev, this)
  	}
  	if IsFalse(And(And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted))) {
  		return fail("precondition failed in CSendPrepare at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>)\n\nlhs: And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)) = %+v\nrhs: Eq(this.state.tmAborted, prev.state.tmAborted) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCSendCommit(r TLA, trace_i int, prev Event, this Event) error {
  
  	if IsFalse(Eq(ToSet(prev.state.tmPrepared.(Seq)), set(str("r1"), str("r2")))) {
  		return fail("precondition failed in CSendCommit at %d; ToSet(tmPrepared) = RM\n\nlhs: ToSet(prev.state.tmPrepared.(Seq)) = %+v\nrhs: set(str(\"r1\"), str(\"r2\")) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, ToSet(prev.state.tmPrepared.(Seq)), set(str("r1"), str("r2")), prev, this)
  	}
  	if IsFalse(And(SetNotIn(record(str("type"), str("Commit"), str("rm"), r), prev.state.msgs.(Set)), Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str("type"), str("Commit"), str("rm"), r)))))) {
  		return fail("precondition failed in CSendCommit at %d; Send([\"type\" |-> \"Commit\", \"rm\" |-> r])\n\nlhs: SetNotIn(record(str(\"type\"), str(\"Commit\"), str(\"rm\"), r), prev.state.msgs.(Set)) = %+v\nrhs: Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str(\"type\"), str(\"Commit\"), str(\"rm\"), r)))) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, SetNotIn(record(str("type"), str("Commit"), str("rm"), r), prev.state.msgs.(Set)), Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str("type"), str("Commit"), str("rm"), r)))), prev, this)
  	}
  	if IsFalse(Eq(this.state.who, str("coordinator"))) {
  		return fail("postcondition failed in CSendCommit at %d; '(who) = \"coordinator\"\n\nlhs: this.state.who = %+v\nrhs: str(\"coordinator\") = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.who, str("coordinator"), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgReceived, None())) {
  		return fail("postcondition failed in CSendCommit at %d; '(lastMsgReceived) = None\n\nlhs: this.state.lastMsgReceived = %+v\nrhs: None() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgReceived, None(), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgSent, Some(record(str("type"), str("Commit"), str("rm"), r)))) {
  		return fail("postcondition failed in CSendCommit at %d; '(lastMsgSent) = Some([\"type\" |-> \"Commit\", \"rm\" |-> r])\n\nlhs: this.state.lastMsgSent = %+v\nrhs: Some(record(str(\"type\"), str(\"Commit\"), str(\"rm\"), r)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgSent, Some(record(str("type"), str("Commit"), str("rm"), r)), prev, this)
  	}
  	if IsFalse(Eq(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed in CSendCommit at %d; UNCHANGED(<<rmState>>)\n\nlhs: this.state.rmState = %+v\nrhs: prev.state.rmState = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.rmState, prev.state.rmState, prev, this)
  	}
  	if IsFalse(And(And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted))) {
  		return fail("precondition failed in CSendCommit at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>)\n\nlhs: And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)) = %+v\nrhs: Eq(this.state.tmAborted, prev.state.tmAborted) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCSendAbort(r TLA, trace_i int, prev Event, this Event) error {
  
  	if IsFalse(Neq(prev.state.tmAborted, seq())) {
  		return fail("precondition failed in CSendAbort at %d; tmAborted /= <<>>\n\nlhs: prev.state.tmAborted = %+v\nrhs: seq() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, prev.state.tmAborted, seq(), prev, this)
  	}
  	if IsFalse(And(SetNotIn(record(str("type"), str("Abort"), str("rm"), r), prev.state.msgs.(Set)), Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str("type"), str("Abort"), str("rm"), r)))))) {
  		return fail("precondition failed in CSendAbort at %d; Send([\"type\" |-> \"Abort\", \"rm\" |-> r])\n\nlhs: SetNotIn(record(str(\"type\"), str(\"Abort\"), str(\"rm\"), r), prev.state.msgs.(Set)) = %+v\nrhs: Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str(\"type\"), str(\"Abort\"), str(\"rm\"), r)))) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, SetNotIn(record(str("type"), str("Abort"), str("rm"), r), prev.state.msgs.(Set)), Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str("type"), str("Abort"), str("rm"), r)))), prev, this)
  	}
  	if IsFalse(Eq(this.state.who, str("coordinator"))) {
  		return fail("postcondition failed in CSendAbort at %d; '(who) = \"coordinator\"\n\nlhs: this.state.who = %+v\nrhs: str(\"coordinator\") = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.who, str("coordinator"), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgReceived, None())) {
  		return fail("postcondition failed in CSendAbort at %d; '(lastMsgReceived) = None\n\nlhs: this.state.lastMsgReceived = %+v\nrhs: None() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgReceived, None(), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgSent, Some(record(str("type"), str("Abort"), str("rm"), r)))) {
  		return fail("postcondition failed in CSendAbort at %d; '(lastMsgSent) = Some([\"type\" |-> \"Abort\", \"rm\" |-> r])\n\nlhs: this.state.lastMsgSent = %+v\nrhs: Some(record(str(\"type\"), str(\"Abort\"), str(\"rm\"), r)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgSent, Some(record(str("type"), str("Abort"), str("rm"), r)), prev, this)
  	}
  	if IsFalse(Eq(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed in CSendAbort at %d; UNCHANGED(<<rmState>>)\n\nlhs: this.state.rmState = %+v\nrhs: prev.state.rmState = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.rmState, prev.state.rmState, prev, this)
  	}
  	if IsFalse(And(And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted))) {
  		return fail("precondition failed in CSendAbort at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>)\n\nlhs: And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)) = %+v\nrhs: Eq(this.state.tmAborted, prev.state.tmAborted) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCReceiveCommit(r TLA, trace_i int, prev Event, this Event) error {
  
  	if IsFalse(SetIn(record(str("type"), str("Committed"), str("rm"), r), prev.state.msgs.(Set))) {
  		return fail("precondition failed in CReceiveCommit at %d; Receive([\"type\" |-> \"Committed\", \"rm\" |-> r])\n\nlhs: record(str(\"type\"), str(\"Committed\"), str(\"rm\"), r) = %+v\nrhs: prev.state.msgs.(Set) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, record(str("type"), str("Committed"), str("rm"), r), prev.state.msgs.(Set), prev, this)
  	}
  	if IsFalse(SetNotIn(r, ToSet(prev.state.tmCommitted.(Seq)))) {
  		return fail("precondition failed in CReceiveCommit at %d; r \\notin ToSet(tmCommitted)\n\nlhs: r = %+v\nrhs: ToSet(prev.state.tmCommitted.(Seq)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, r, ToSet(prev.state.tmCommitted.(Seq)), prev, this)
  	}
  	if IsFalse(Eq(this.state.who, str("coordinator"))) {
  		return fail("postcondition failed in CReceiveCommit at %d; '(who) = \"coordinator\"\n\nlhs: this.state.who = %+v\nrhs: str(\"coordinator\") = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.who, str("coordinator"), prev, this)
  	}
  	if IsFalse(Eq(this.state.tmCommitted, Append(prev.state.tmCommitted.(Seq), r.(Seq)))) {
  		return fail("postcondition failed in CReceiveCommit at %d; '(tmCommitted) = Append(tmCommitted, r)\n\nlhs: this.state.tmCommitted = %+v\nrhs: Append(prev.state.tmCommitted.(Seq), r.(Seq)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.tmCommitted, Append(prev.state.tmCommitted.(Seq), r.(Seq)), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgReceived, Some(record(str("type"), str("Committed"), str("rm"), r)))) {
  		return fail("postcondition failed in CReceiveCommit at %d; '(lastMsgReceived) = Some([\"type\" |-> \"Committed\", \"rm\" |-> r])\n\nlhs: this.state.lastMsgReceived = %+v\nrhs: Some(record(str(\"type\"), str(\"Committed\"), str(\"rm\"), r)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgReceived, Some(record(str("type"), str("Committed"), str("rm"), r)), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgSent, None())) {
  		return fail("postcondition failed in CReceiveCommit at %d; '(lastMsgSent) = None\n\nlhs: this.state.lastMsgSent = %+v\nrhs: None() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgSent, None(), prev, this)
  	}
  	if IsFalse(Eq(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed in CReceiveCommit at %d; UNCHANGED(<<rmState>>)\n\nlhs: this.state.rmState = %+v\nrhs: prev.state.rmState = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.rmState, prev.state.rmState, prev, this)
  	}
  	if IsFalse(And(And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.msgs, prev.state.msgs)), Eq(this.state.tmAborted, prev.state.tmAborted))) {
  		return fail("precondition failed in CReceiveCommit at %d; UNCHANGED(<<tmPrepared, msgs, tmAborted>>)\n\nlhs: And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.msgs, prev.state.msgs)) = %+v\nrhs: Eq(this.state.tmAborted, prev.state.tmAborted) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.msgs, prev.state.msgs)), Eq(this.state.tmAborted, prev.state.tmAborted), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCReceiveAbort(r TLA, trace_i int, prev Event, this Event) error {
  
  	if IsFalse(SetIn(record(str("type"), str("Aborted"), str("rm"), r), prev.state.msgs.(Set))) {
  		return fail("precondition failed in CReceiveAbort at %d; Receive([\"type\" |-> \"Aborted\", \"rm\" |-> r])\n\nlhs: record(str(\"type\"), str(\"Aborted\"), str(\"rm\"), r) = %+v\nrhs: prev.state.msgs.(Set) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, record(str("type"), str("Aborted"), str("rm"), r), prev.state.msgs.(Set), prev, this)
  	}
  	if IsFalse(SetNotIn(r, ToSet(prev.state.tmAborted.(Seq)))) {
  		return fail("precondition failed in CReceiveAbort at %d; r \\notin ToSet(tmAborted)\n\nlhs: r = %+v\nrhs: ToSet(prev.state.tmAborted.(Seq)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, r, ToSet(prev.state.tmAborted.(Seq)), prev, this)
  	}
  	if IsFalse(Eq(this.state.who, str("coordinator"))) {
  		return fail("postcondition failed in CReceiveAbort at %d; '(who) = \"coordinator\"\n\nlhs: this.state.who = %+v\nrhs: str(\"coordinator\") = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.who, str("coordinator"), prev, this)
  	}
  	if IsFalse(Eq(this.state.tmAborted, Append(prev.state.tmAborted.(Seq), r.(Seq)))) {
  		return fail("postcondition failed in CReceiveAbort at %d; '(tmAborted) = Append(tmAborted, r)\n\nlhs: this.state.tmAborted = %+v\nrhs: Append(prev.state.tmAborted.(Seq), r.(Seq)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.tmAborted, Append(prev.state.tmAborted.(Seq), r.(Seq)), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgReceived, Some(record(str("type"), str("Aborted"), str("rm"), r)))) {
  		return fail("postcondition failed in CReceiveAbort at %d; '(lastMsgReceived) = Some([\"type\" |-> \"Aborted\", \"rm\" |-> r])\n\nlhs: this.state.lastMsgReceived = %+v\nrhs: Some(record(str(\"type\"), str(\"Aborted\"), str(\"rm\"), r)) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgReceived, Some(record(str("type"), str("Aborted"), str("rm"), r)), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgSent, None())) {
  		return fail("postcondition failed in CReceiveAbort at %d; '(lastMsgSent) = None\n\nlhs: this.state.lastMsgSent = %+v\nrhs: None() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgSent, None(), prev, this)
  	}
  	if IsFalse(Eq(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed in CReceiveAbort at %d; UNCHANGED(<<rmState>>)\n\nlhs: this.state.rmState = %+v\nrhs: prev.state.rmState = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.rmState, prev.state.rmState, prev, this)
  	}
  	if IsFalse(And(And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.msgs, prev.state.msgs)), Eq(this.state.tmCommitted, prev.state.tmCommitted))) {
  		return fail("precondition failed in CReceiveAbort at %d; UNCHANGED(<<tmPrepared, msgs, tmCommitted>>)\n\nlhs: And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.msgs, prev.state.msgs)) = %+v\nrhs: Eq(this.state.tmCommitted, prev.state.tmCommitted) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.msgs, prev.state.msgs)), Eq(this.state.tmCommitted, prev.state.tmCommitted), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckPHandlePrepare(r TLA, trace_i int, prev Event, this Event) error {
  
  	if IsFalse(Eq(RecordIndex(prev.state.rmState.(Record), r.(String)), str("working"))) {
  		return fail("precondition failed in PHandlePrepare at %d; rmState[r] = \"working\"\n\nlhs: RecordIndex(prev.state.rmState.(Record), r.(String)) = %+v\nrhs: str(\"working\") = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, RecordIndex(prev.state.rmState.(Record), r.(String)), str("working"), prev, this)
  	}
  	if IsFalse(SetIn(record(str("type"), str("Prepare"), str("rm"), r), prev.state.msgs.(Set))) {
  		return fail("precondition failed in PHandlePrepare at %d; Receive([\"type\" |-> \"Prepare\", \"rm\" |-> r])\n\nlhs: record(str(\"type\"), str(\"Prepare\"), str(\"rm\"), r) = %+v\nrhs: prev.state.msgs.(Set) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, record(str("type"), str("Prepare"), str("rm"), r), prev.state.msgs.(Set), prev, this)
  	}
  	if IsFalse(Eq(this.state.rmState, Except(prev.state.rmState.(Record), r.(String), str("prepared")))) {
  		return fail("postcondition failed in PHandlePrepare at %d; '(rmState) = [rmState EXCEPT ![r] = \"prepared\"]\n\nlhs: this.state.rmState = %+v\nrhs: Except(prev.state.rmState.(Record), r.(String), str(\"prepared\")) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.rmState, Except(prev.state.rmState.(Record), r.(String), str("prepared")), prev, this)
  	}
  	if IsFalse(And(SetNotIn(record(str("type"), str("Prepared"), str("rm"), r), prev.state.msgs.(Set)), Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str("type"), str("Prepared"), str("rm"), r)))))) {
  		return fail("precondition failed in PHandlePrepare at %d; Send([\"type\" |-> \"Prepared\", \"rm\" |-> r])\n\nlhs: SetNotIn(record(str(\"type\"), str(\"Prepared\"), str(\"rm\"), r), prev.state.msgs.(Set)) = %+v\nrhs: Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str(\"type\"), str(\"Prepared\"), str(\"rm\"), r)))) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, SetNotIn(record(str("type"), str("Prepared"), str("rm"), r), prev.state.msgs.(Set)), Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str("type"), str("Prepared"), str("rm"), r)))), prev, this)
  	}
  	if IsFalse(Eq(this.state.who, r)) {
  		return fail("postcondition failed in PHandlePrepare at %d; '(who) = r\n\nlhs: this.state.who = %+v\nrhs: r = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.who, r, prev, this)
  	}
  	if IsFalse(And(Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived), Eq(this.state.lastMsgSent, prev.state.lastMsgSent))) {
  		return fail("precondition failed in PHandlePrepare at %d; UNCHANGED(<<lastMsgReceived, lastMsgSent>>)\n\nlhs: Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived) = %+v\nrhs: Eq(this.state.lastMsgSent, prev.state.lastMsgSent) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived), Eq(this.state.lastMsgSent, prev.state.lastMsgSent), prev, this)
  	}
  	if IsFalse(And(And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted))) {
  		return fail("precondition failed in PHandlePrepare at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>)\n\nlhs: And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)) = %+v\nrhs: Eq(this.state.tmAborted, prev.state.tmAborted) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckPHandleCommit(r TLA, trace_i int, prev Event, this Event) error {
  
  	if IsFalse(Eq(RecordIndex(prev.state.rmState.(Record), r.(String)), str("prepared"))) {
  		return fail("precondition failed in PHandleCommit at %d; rmState[r] = \"prepared\"\n\nlhs: RecordIndex(prev.state.rmState.(Record), r.(String)) = %+v\nrhs: str(\"prepared\") = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, RecordIndex(prev.state.rmState.(Record), r.(String)), str("prepared"), prev, this)
  	}
  	if IsFalse(SetIn(record(str("type"), str("Commit"), str("rm"), r), prev.state.msgs.(Set))) {
  		return fail("precondition failed in PHandleCommit at %d; Receive([\"type\" |-> \"Commit\", \"rm\" |-> r])\n\nlhs: record(str(\"type\"), str(\"Commit\"), str(\"rm\"), r) = %+v\nrhs: prev.state.msgs.(Set) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, record(str("type"), str("Commit"), str("rm"), r), prev.state.msgs.(Set), prev, this)
  	}
  	if IsFalse(Eq(this.state.rmState, Except(prev.state.rmState.(Record), r.(String), str("committed")))) {
  		return fail("postcondition failed in PHandleCommit at %d; '(rmState) = [rmState EXCEPT ![r] = \"committed\"]\n\nlhs: this.state.rmState = %+v\nrhs: Except(prev.state.rmState.(Record), r.(String), str(\"committed\")) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.rmState, Except(prev.state.rmState.(Record), r.(String), str("committed")), prev, this)
  	}
  	if IsFalse(And(SetNotIn(record(str("type"), str("Committed"), str("rm"), r), prev.state.msgs.(Set)), Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str("type"), str("Committed"), str("rm"), r)))))) {
  		return fail("precondition failed in PHandleCommit at %d; Send([\"type\" |-> \"Committed\", \"rm\" |-> r])\n\nlhs: SetNotIn(record(str(\"type\"), str(\"Committed\"), str(\"rm\"), r), prev.state.msgs.(Set)) = %+v\nrhs: Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str(\"type\"), str(\"Committed\"), str(\"rm\"), r)))) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, SetNotIn(record(str("type"), str("Committed"), str("rm"), r), prev.state.msgs.(Set)), Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str("type"), str("Committed"), str("rm"), r)))), prev, this)
  	}
  	if IsFalse(Eq(this.state.who, r)) {
  		return fail("postcondition failed in PHandleCommit at %d; '(who) = r\n\nlhs: this.state.who = %+v\nrhs: r = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.who, r, prev, this)
  	}
  	if IsFalse(And(Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived), Eq(this.state.lastMsgSent, prev.state.lastMsgSent))) {
  		return fail("precondition failed in PHandleCommit at %d; UNCHANGED(<<lastMsgReceived, lastMsgSent>>)\n\nlhs: Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived) = %+v\nrhs: Eq(this.state.lastMsgSent, prev.state.lastMsgSent) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived), Eq(this.state.lastMsgSent, prev.state.lastMsgSent), prev, this)
  	}
  	if IsFalse(And(And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted))) {
  		return fail("precondition failed in PHandleCommit at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>)\n\nlhs: And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)) = %+v\nrhs: Eq(this.state.tmAborted, prev.state.tmAborted) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckPHandleAbort(r TLA, trace_i int, prev Event, this Event) error {
  
  	if IsFalse(SetIn(RecordIndex(prev.state.rmState.(Record), r.(String)), set(str("working"), str("prepared")))) {
  		return fail("precondition failed in PHandleAbort at %d; rmState[r] \\in {\"working\", \"prepared\"}\n\nlhs: RecordIndex(prev.state.rmState.(Record), r.(String)) = %+v\nrhs: set(str(\"working\"), str(\"prepared\")) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, RecordIndex(prev.state.rmState.(Record), r.(String)), set(str("working"), str("prepared")), prev, this)
  	}
  	if IsFalse(SetIn(record(str("type"), str("Abort"), str("rm"), r), prev.state.msgs.(Set))) {
  		return fail("precondition failed in PHandleAbort at %d; Receive([\"type\" |-> \"Abort\", \"rm\" |-> r])\n\nlhs: record(str(\"type\"), str(\"Abort\"), str(\"rm\"), r) = %+v\nrhs: prev.state.msgs.(Set) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, record(str("type"), str("Abort"), str("rm"), r), prev.state.msgs.(Set), prev, this)
  	}
  	if IsFalse(Eq(this.state.rmState, Except(prev.state.rmState.(Record), r.(String), str("aborted")))) {
  		return fail("postcondition failed in PHandleAbort at %d; '(rmState) = [rmState EXCEPT ![r] = \"aborted\"]\n\nlhs: this.state.rmState = %+v\nrhs: Except(prev.state.rmState.(Record), r.(String), str(\"aborted\")) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.rmState, Except(prev.state.rmState.(Record), r.(String), str("aborted")), prev, this)
  	}
  	if IsFalse(Eq(this.state.who, r)) {
  		return fail("postcondition failed in PHandleAbort at %d; '(who) = r\n\nlhs: this.state.who = %+v\nrhs: r = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.who, r, prev, this)
  	}
  	if IsFalse(And(SetNotIn(record(str("type"), str("Aborted"), str("rm"), r), prev.state.msgs.(Set)), Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str("type"), str("Aborted"), str("rm"), r)))))) {
  		return fail("precondition failed in PHandleAbort at %d; Send([\"type\" |-> \"Aborted\", \"rm\" |-> r])\n\nlhs: SetNotIn(record(str(\"type\"), str(\"Aborted\"), str(\"rm\"), r), prev.state.msgs.(Set)) = %+v\nrhs: Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str(\"type\"), str(\"Aborted\"), str(\"rm\"), r)))) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, SetNotIn(record(str("type"), str("Aborted"), str("rm"), r), prev.state.msgs.(Set)), Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str("type"), str("Aborted"), str("rm"), r)))), prev, this)
  	}
  	if IsFalse(And(Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived), Eq(this.state.lastMsgSent, prev.state.lastMsgSent))) {
  		return fail("precondition failed in PHandleAbort at %d; UNCHANGED(<<lastMsgReceived, lastMsgSent>>)\n\nlhs: Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived) = %+v\nrhs: Eq(this.state.lastMsgSent, prev.state.lastMsgSent) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived), Eq(this.state.lastMsgSent, prev.state.lastMsgSent), prev, this)
  	}
  	if IsFalse(And(And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted))) {
  		return fail("precondition failed in PHandleAbort at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>)\n\nlhs: And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)) = %+v\nrhs: Eq(this.state.tmAborted, prev.state.tmAborted) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckPSpontaneouslyAbort(r TLA, trace_i int, prev Event, this Event) error {
  
  	if IsFalse(SetIn(RecordIndex(prev.state.rmState.(Record), r.(String)), set(str("working"), str("prepared")))) {
  		return fail("precondition failed in PSpontaneouslyAbort at %d; rmState[r] \\in {\"working\", \"prepared\"}\n\nlhs: RecordIndex(prev.state.rmState.(Record), r.(String)) = %+v\nrhs: set(str(\"working\"), str(\"prepared\")) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, RecordIndex(prev.state.rmState.(Record), r.(String)), set(str("working"), str("prepared")), prev, this)
  	}
  	if IsFalse(Eq(this.state.rmState, Except(prev.state.rmState.(Record), r.(String), str("aborted")))) {
  		return fail("postcondition failed in PSpontaneouslyAbort at %d; '(rmState) = [rmState EXCEPT ![r] = \"aborted\"]\n\nlhs: this.state.rmState = %+v\nrhs: Except(prev.state.rmState.(Record), r.(String), str(\"aborted\")) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.rmState, Except(prev.state.rmState.(Record), r.(String), str("aborted")), prev, this)
  	}
  	if IsFalse(Eq(this.state.who, r)) {
  		return fail("postcondition failed in PSpontaneouslyAbort at %d; '(who) = r\n\nlhs: this.state.who = %+v\nrhs: r = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.who, r, prev, this)
  	}
  	if IsFalse(And(SetNotIn(record(str("type"), str("Aborted"), str("rm"), r), prev.state.msgs.(Set)), Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str("type"), str("Aborted"), str("rm"), r)))))) {
  		return fail("precondition failed in PSpontaneouslyAbort at %d; Send([\"type\" |-> \"Aborted\", \"rm\" |-> r])\n\nlhs: SetNotIn(record(str(\"type\"), str(\"Aborted\"), str(\"rm\"), r), prev.state.msgs.(Set)) = %+v\nrhs: Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str(\"type\"), str(\"Aborted\"), str(\"rm\"), r)))) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, SetNotIn(record(str("type"), str("Aborted"), str("rm"), r), prev.state.msgs.(Set)), Eq(this.state.msgs, SetUnion(prev.state.msgs.(Set), set(record(str("type"), str("Aborted"), str("rm"), r)))), prev, this)
  	}
  	if IsFalse(And(Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived), Eq(this.state.lastMsgSent, prev.state.lastMsgSent))) {
  		return fail("precondition failed in PSpontaneouslyAbort at %d; UNCHANGED(<<lastMsgReceived, lastMsgSent>>)\n\nlhs: Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived) = %+v\nrhs: Eq(this.state.lastMsgSent, prev.state.lastMsgSent) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived), Eq(this.state.lastMsgSent, prev.state.lastMsgSent), prev, this)
  	}
  	if IsFalse(And(And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted))) {
  		return fail("precondition failed in PSpontaneouslyAbort at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>)\n\nlhs: And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)) = %+v\nrhs: Eq(this.state.tmAborted, prev.state.tmAborted) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted), prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckCReset(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(BoundedForall(set(str("r1"), str("r2")), func(v0 TLA) Bool {
  		return SetIn(record(str("type"), str("Committed"), str("rm"), v0), prev.state.msgs.(Set))
  	})) {
  
  		if IsFalse(BoundedForall(set(str("r1"), str("r2")), func(v1 TLA) Bool {
  			return SetIn(record(str("type"), str("Aborted"), str("rm"), v1), prev.state.msgs.(Set))
  		})) {
  			return fail("precondition failed in CReset at %d; (\\A r \\in RM : [\"type\" |-> \"Committed\", \"rm\" |-> r] \\in msgs \\/ \\A r \\in RM : [\"type\" |-> \"Aborted\", \"rm\" |-> r] \\in msgs)\n\nlhs: set(str(\"r1\"), str(\"r2\")) = %+v\nrhs: \"<func>\" = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, set(str("r1"), str("r2")), "<func>", prev, this)
  		}
  	}
  
  	if IsFalse(Eq(this.state.lastMsgReceived, None())) {
  		return fail("postcondition failed in CReset at %d; '(lastMsgReceived) = None\n\nlhs: this.state.lastMsgReceived = %+v\nrhs: None() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgReceived, None(), prev, this)
  	}
  	if IsFalse(Eq(this.state.lastMsgSent, None())) {
  		return fail("postcondition failed in CReset at %d; '(lastMsgSent) = None\n\nlhs: this.state.lastMsgSent = %+v\nrhs: None() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.lastMsgSent, None(), prev, this)
  	}
  	if IsFalse(Eq(this.state.tmPrepared, seq())) {
  		return fail("postcondition failed in CReset at %d; '(tmPrepared) = <<>>\n\nlhs: this.state.tmPrepared = %+v\nrhs: seq() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.tmPrepared, seq(), prev, this)
  	}
  	if IsFalse(Eq(this.state.tmCommitted, seq())) {
  		return fail("postcondition failed in CReset at %d; '(tmCommitted) = <<>>\n\nlhs: this.state.tmCommitted = %+v\nrhs: seq() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.tmCommitted, seq(), prev, this)
  	}
  	if IsFalse(Eq(this.state.tmAborted, seq())) {
  		return fail("postcondition failed in CReset at %d; '(tmAborted) = <<>>\n\nlhs: this.state.tmAborted = %+v\nrhs: seq() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.tmAborted, seq(), prev, this)
  	}
  	if IsFalse(Eq(this.state.msgs, set())) {
  		return fail("postcondition failed in CReset at %d; '(msgs) = {}\n\nlhs: this.state.msgs = %+v\nrhs: set() = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.msgs, set(), prev, this)
  	}
  	if IsFalse(Eq(this.state.rmState, prev.state.rmState)) {
  		return fail("precondition failed in CReset at %d; UNCHANGED(<<rmState>>)\n\nlhs: this.state.rmState = %+v\nrhs: prev.state.rmState = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.rmState, prev.state.rmState, prev, this)
  	}
  	return nil
  }
  
  func (m *Monitor) CheckPReset(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(BoundedForall(set(str("r1"), str("r2")), func(v2 TLA) Bool { return Eq(RecordIndex(prev.state.rmState.(Record), v2.(String)), str("aborted")) })) {
  
  		if IsFalse(BoundedForall(set(str("r1"), str("r2")), func(v3 TLA) Bool { return Eq(RecordIndex(prev.state.rmState.(Record), v3.(String)), str("committed")) })) {
  			return fail("precondition failed in PReset at %d; (\\A r \\in RM : rmState[r] = \"aborted\" \\/ \\A r \\in RM : rmState[r] = \"committed\")\n\nlhs: set(str(\"r1\"), str(\"r2\")) = %+v\nrhs: \"<func>\" = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, set(str("r1"), str("r2")), "<func>", prev, this)
  		}
  	}
  
  	if IsFalse(Eq(this.state.rmState, FnConstruct(set(str("r1"), str("r2")), func(_ TLA) TLA { return str("working") }))) {
  		return fail("postcondition failed in PReset at %d; '(rmState) = [ r \\in RM |-> \"working\" ]\n\nlhs: this.state.rmState = %+v\nrhs: FnConstruct(set(str(\"r1\"), str(\"r2\")), func(_ TLA) TLA { return str(\"working\") }) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.rmState, FnConstruct(set(str("r1"), str("r2")), func(_ TLA) TLA { return str("working") }), prev, this)
  	}
  	if IsFalse(Eq(this.state.who, str("none"))) {
  		return fail("postcondition failed in PReset at %d; '(who) = \"none\"\n\nlhs: this.state.who = %+v\nrhs: str(\"none\") = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.who, str("none"), prev, this)
  	}
  	if IsFalse(And(Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived), Eq(this.state.lastMsgSent, prev.state.lastMsgSent))) {
  		return fail("precondition failed in PReset at %d; UNCHANGED(<<lastMsgReceived, lastMsgSent>>)\n\nlhs: Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived) = %+v\nrhs: Eq(this.state.lastMsgSent, prev.state.lastMsgSent) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, Eq(this.state.lastMsgReceived, prev.state.lastMsgReceived), Eq(this.state.lastMsgSent, prev.state.lastMsgSent), prev, this)
  	}
  	if IsFalse(And(And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted))) {
  		return fail("precondition failed in PReset at %d; UNCHANGED(<<tmPrepared, tmCommitted, tmAborted>>)\n\nlhs: And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)) = %+v\nrhs: Eq(this.state.tmAborted, prev.state.tmAborted) = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, And(Eq(this.state.tmPrepared, prev.state.tmPrepared), Eq(this.state.tmCommitted, prev.state.tmCommitted)), Eq(this.state.tmAborted, prev.state.tmAborted), prev, this)
  	}
  	if IsFalse(Eq(this.state.msgs, prev.state.msgs)) {
  		return fail("precondition failed in PReset at %d; UNCHANGED(<<msgs>>)\n\nlhs: this.state.msgs = %+v\nrhs: prev.state.msgs = %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.msgs, prev.state.msgs, prev, this)
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
  func (m *Monitor) CaptureVariable(v State, typ EventType, args ...TLA) error {
  
  	e := Event{
  		typ:    typ,
  		params: args,
  		state:  v,
  		// no need to capture file and line here
  	}
  	m.extra = append(m.extra, e)
  	return nil
  }
  
  func (m *Monitor) CaptureState(c State, typ EventType, args ...TLA) error {
  
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
