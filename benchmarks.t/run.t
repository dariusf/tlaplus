
  $ source ../build.sh; tla2tools=../tlatools/org.lamport.tlatools/dist/tla2tools.jar

  $ pluscal -label Par.tla | make_det
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans -label Par.tla
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
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar pcal.trans -label Chor.tla
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

  $ monitor_check_show Stress
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar tlc2.TLC -monitor Stress.tla
  988 lines
  parse ok
  compile ok
  package monitoring
  
  import (
  	// "encoding/json"
  	"fmt"
  	"math"
  	"path"
  	"reflect"
  	"runtime"
  	"sort"
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
  	keys := []string{}
  	for k := range s.elements {
  		keys = append(keys, k)
  	}
  	sort.Strings(keys)
  
  	ss := []string{}
  	for _, k := range keys {
  		v := s.elements[k]
  		ss = append(ss, fmt.Sprintf("%s |-> %s", k, v.String()))
  	}
  	return fmt.Sprintf("[%s]", strings.Join(ss, ", "))
  }
  
  type Set struct {
  	elements map[string]TLA
  }
  
  func (s Set) String() string {
  	keys := []string{}
  	for k := range s.elements {
  		keys = append(keys, k)
  	}
  	sort.Strings(keys)
  
  	ss := []string{}
  	for _, k := range keys {
  		v := s.elements[k]
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
  	// avoid nil slice vs empty slice shenanigans
  	if len(elts) == 0 {
  		elts = []TLA{}
  	}
  	res := map[string]TLA{}
  	for _, v := range elts {
  		res[hash(v)] = v
  	}
  	return Set{elements: res}
  }
  
  func record(kvs ...TLA) Record {
  	// avoid nil slice vs empty slice shenanigans
  	if len(kvs) == 0 {
  		kvs = []TLA{}
  	}
  	res := map[string]TLA{}
  	for i := 0; i < len(kvs); i += 2 {
  		res[kvs[i].(String).value] = kvs[i+1]
  	}
  	return Record{elements: res}
  }
  
  func seq(elts ...TLA) Seq {
  	// avoid nil slice vs empty slice shenanigans
  	if len(elts) == 0 {
  		elts = []TLA{}
  	}
  	return Seq{elements: elts}
  }
  
  // library
  
  func Some(a TLA) Seq {
  	return seq(a)
  }
  
  func None() Seq {
  	return seq()
  }
  
  func Append(a Seq, b TLA) Seq {
  	return Seq{elements: append(a.elements, b)}
  }
  
  func AppendSeqs(a Seq, b Seq) Seq {
  	return Seq{elements: append(a.elements, b.elements...)}
  }
  
  func Len(a Seq) Int {
  	return integer(len(a.elements))
  }
  
  func Cardinality(a Set) Int {
  	return integer(len(a.elements))
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
  
  func TLAIndex(i int) int {
  	return i - 1
  }
  
  func SeqIndex(a Seq, b Int) TLA {
  	return a.elements[TLAIndex(b.value)]
  }
  
  func IndexInto(a TLA, b TLA) TLA {
  	a1, ok1 := a.(Seq)
  	b1, ok2 := b.(Int)
  	if ok1 && ok2 {
  		return SeqIndex(a1, b1)
  	} else {
  		return RecordIndex(a.(Record), b.(String))
  	}
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
  
  func IntDiv(a Int, b Int) Int {
  	return Int{value: a.value / b.value}
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
  		res = res && IsTrue(f(v))
  	}
  	return Bool{value: res}
  }
  
  func BoundedExists(set Set, f func(TLA) Bool) Bool {
  	res := false
  	for _, v := range set.elements {
  		res = res || IsTrue(f(v))
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
  
  func FoldSeq(f func(TLA, TLA) TLA, base TLA, seq Seq) TLA {
  	res := base
  	for _, v := range seq.elements {
  		res = f(v, res)
  	}
  	return res
  }
  
  func Remove(s Seq, e TLA) Seq {
  	res := []TLA{}
  	for _, v := range s.elements {
  		if IsFalse(Eq(v, e)) {
  			res = append(res, v)
  		}
  	}
  	return seq(res...)
  }
  
  func RemoveAt(s Seq, i Int) Seq {
  	res := []TLA{}
  	for j, v := range s.elements {
  		if TLAIndex(i.value) != j {
  			res = append(res, v)
  		}
  	}
  	return seq(res...)
  }
  
  func SetToSeq(set Set) Seq {
  	res := []TLA{}
  	for _, v := range set.elements {
  		res = append(res, v)
  	}
  	return seq(res...)
  }
  
  func Min(set Set) Int {
  	res := math.MaxInt
  	for _, v := range set.elements {
  		if v.(Int).value < res {
  			res = v.(Int).value
  		}
  	}
  	return integer(res)
  }
  
  func Max(set Set) Int {
  	res := math.MinInt
  	for _, v := range set.elements {
  		if v.(Int).value > res {
  			res = v.(Int).value
  		}
  	}
  	return integer(res)
  }
  
  func IsPrefix(prefix Seq, seq Seq) Bool {
  	for i := 0; i < len(prefix.elements); i++ {
  		if IsFalse(Eq(prefix.elements[i], seq.elements[i])) {
  			return boolean(false)
  		}
  	}
  	return boolean(true)
  }
  
  func SelectSeq(s Seq, f func(TLA) TLA) Seq {
  	res := []TLA{}
  	for _, v := range s.elements {
  		if IsTrue(f(v)) {
  			res = append(res, v)
  		}
  	}
  	return seq(res...)
  }
  
  func RangeIncl(lower Int, upper Int) Set {
  	res := []TLA{}
  	for i := lower.value; i <= upper.value; i++ {
  		res = append(res, integer(i))
  	}
  	return set(res...)
  }
  
  // panic instead of returning error
  var crash = true
  
  func hash(a TLA) string {
  	return a.String()
  }
  
  // this does not guarantee keys are sorted, which is a problem since map traversal is nondet
  // func hash(a any) string {
  // 	return fmt.Sprintf("%+v", a)
  // }
  
  // this doesn't work for maps with non-string keys
  // func hash(a any) string {
  // 	s, _ := json.Marshal(a)
  // 	return string(s)
  // }
  
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
  	SendM
  	C1
  	D
  	E
  	F
  	G
  	H
  	H1
  	H2
  	H3
  	H4
  	a
  	b
  	c
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
  	case SendM:
  		return "SendM"
  	case C1:
  		return "C1"
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
  	case a:
  		return "a"
  	case b:
  		return "b"
  	case c:
  		return "c"
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
  
  func NewMonitor( /* constants Constants */ ) Monitor {
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
  		case SendM:
  			if err := m.CheckSendM(this.params[0], i, prev, this); err != nil {
  				return err
  			}
  		case C1:
  			if err := m.CheckC1(i, prev, this); err != nil {
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
  		case a:
  			if err := m.Checka(i, prev, this); err != nil {
  				return err
  			}
  		case b:
  			if err := m.Checkb(i, prev, this); err != nil {
  				return err
  			}
  		case c:
  			if err := m.Checkc(i, prev, this); err != nil {
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
  
  	// x = 1
  	if IsFalse(Eq(this.state.x, integer(1))) {
  		return fail("precondition failed in initial at %d; x = 1\n\nlhs: this.state.x\n\n= %+v\n\nrhs: integer(1)\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.x, integer(1), prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckA(trace_i int, prev Event, this Event) error {
  
  	// x < 0
  	if IsFalse(IntLt(any(prev.state.x).(Int), integer(0))) {
  		return fail("precondition failed in A at %d; x < 0\n\nlhs: any(prev.state.x).(Int)\n\n= %+v\n\nrhs: integer(0)\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, any(prev.state.x).(Int), integer(0), prev, this)
  	}
  
  	// x' = x + 1
  	if IsFalse(Eq(this.state.x, IntPlus(any(prev.state.x).(Int), integer(1)))) {
  		return fail("postcondition failed in A at %d; x' = x + 1\n\nlhs: this.state.x\n\n= %+v\n\nrhs: IntPlus(any(prev.state.x).(Int), integer(1))\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.x, IntPlus(any(prev.state.x).(Int), integer(1)), prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckA1(trace_i int, prev Event, this Event) error {
  
  	// x < 0
  	if IsFalse(IntLt(any(prev.state.x).(Int), integer(0))) {
  		return fail("precondition failed in A1 at %d; x < 0\n\nlhs: any(prev.state.x).(Int)\n\n= %+v\n\nrhs: integer(0)\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, any(prev.state.x).(Int), integer(0), prev, this)
  	}
  
  	// x' = x + 1 \land x < 0
  	if IsFalse(And(Eq(this.state.x, IntPlus(any(prev.state.x).(Int), integer(1))), IntLt(any(prev.state.x).(Int), integer(0)))) {
  		return fail("precondition failed in A1 at %d; x' = x + 1 \\land x < 0\n\nlhs: Eq(this.state.x, IntPlus(any(prev.state.x).(Int), integer(1)))\n\n= %+v\n\nrhs: IntLt(any(prev.state.x).(Int), integer(0))\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, Eq(this.state.x, IntPlus(any(prev.state.x).(Int), integer(1))), IntLt(any(prev.state.x).(Int), integer(0)), prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckB(trace_i int, prev Event, this Event) error {
  
  	// UNCHANGED(x)
  	if IsFalse(Eq(this.state.x, prev.state.x)) {
  		return fail("precondition failed in B at %d; UNCHANGED(x)\n\nlhs: this.state.x\n\n= %+v\n\nrhs: prev.state.x\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.x, prev.state.x, prev, this)
  	}
  
  	// UNCHANGED(vars)
  	if IsFalse(Eq(this.state.x, prev.state.x)) {
  		return fail("precondition failed in B at %d; UNCHANGED(vars)\n\nlhs: this.state.x\n\n= %+v\n\nrhs: prev.state.x\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.x, prev.state.x, prev, this)
  	}
  
  	// UNCHANGED(<<x>>)
  	if IsFalse(Eq(this.state.x, prev.state.x)) {
  		return fail("precondition failed in B at %d; UNCHANGED(<<x>>)\n\nlhs: this.state.x\n\n= %+v\n\nrhs: prev.state.x\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, this.state.x, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckC(trace_i int, prev Event, this Event) error {
  
  	// Send(x)
  	if IsFalse(Eq(prev.state.x, prev.state.x)) {
  		return fail("precondition failed in C at %d; Send(x)\n\nlhs: prev.state.x\n\n= %+v\n\nrhs: prev.state.x\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, prev.state.x, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckSendM(y TLA, trace_i int, prev Event, this Event) error {
  
  	// Send(y)
  	if IsFalse(Eq(prev.state.x, y)) {
  		return fail("precondition failed in SendM at %d; Send(y)\n\nlhs: prev.state.x\n\n= %+v\n\nrhs: y\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, prev.state.x, y, prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckC1(trace_i int, prev Event, this Event) error {
  
  	// SendM(x)
  	if IsFalse(Eq(prev.state.x, prev.state.x)) {
  		return fail("precondition failed in C1 at %d; SendM(x)\n\nlhs: prev.state.x\n\n= %+v\n\nrhs: prev.state.x\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, prev.state.x, prev.state.x, prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckD(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(And(Eq(prev.state.x, integer(1)), Eq(this.state.x, integer(2)))) {
  
  		// ((x = 1 /\ x' = 2) \/ (x /= 1 /\ x' = 3))
  		if IsFalse(And(Neq(prev.state.x, integer(1)), Eq(this.state.x, integer(3)))) {
  			return fail("precondition failed in D at %d; ((x = 1 /\\ x' = 2) \\/ (x /= 1 /\\ x' = 3))\n\nlhs: Neq(prev.state.x, integer(1))\n\n= %+v\n\nrhs: Eq(this.state.x, integer(3))\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, Neq(prev.state.x, integer(1)), Eq(this.state.x, integer(3)), prev, this)
  		}
  	}
  
  	return nil
  }
  
  func (monitor *Monitor) CheckE(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(And(And(Eq(prev.state.x, integer(1)), Eq(this.state.x, integer(2))), Or(Eq(prev.state.x, integer(2)), And(Eq(prev.state.x, integer(3)), Eq(prev.state.x, integer(1)))))) {
  
  		// ((x = 1 /\ x' = 2) \/ (x /= 1 /\ x' = 3))
  		if IsFalse(And(Neq(prev.state.x, integer(1)), Eq(this.state.x, integer(3)))) {
  			return fail("precondition failed in E at %d; ((x = 1 /\\ x' = 2) \\/ (x /= 1 /\\ x' = 3))\n\nlhs: Neq(prev.state.x, integer(1))\n\n= %+v\n\nrhs: Eq(this.state.x, integer(3))\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, Neq(prev.state.x, integer(1)), Eq(this.state.x, integer(3)), prev, this)
  		}
  	}
  
  	return nil
  }
  
  func (monitor *Monitor) CheckF(z TLA, trace_i int, prev Event, this Event) error {
  
  	// TRUE
  	if IsFalse(boolean(true)) {
  		return fail("precondition failed in F at %d; TRUE\n\nlhs: \"<none>\"\n\n= %+v\n\nrhs: \"<none>\"\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, "<none>", "<none>", prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckG(trace_i int, prev Event, this Event) error {
  
  	// [["a" |-> 1] EXCEPT !["a"] = 2]["a"] = 2
  	if IsFalse(Eq(IndexInto(Except(record(str("a"), integer(1)), str("a"), integer(2)), str("a")), integer(2))) {
  		return fail("precondition failed in G at %d; [[\"a\" |-> 1] EXCEPT ![\"a\"] = 2][\"a\"] = 2\n\nlhs: IndexInto(Except(record(str(\"a\"), integer(1)), str(\"a\"), integer(2)), str(\"a\"))\n\n= %+v\n\nrhs: integer(2)\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, IndexInto(Except(record(str("a"), integer(1)), str("a"), integer(2)), str("a")), integer(2), prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckH(trace_i int, prev Event, this Event) error {
  
  	// \A r \in {1, 2} : r = 1
  	if IsFalse(BoundedForall(set(integer(1), integer(2)), func(v0_r TLA) Bool { return Eq(v0_r, integer(1)) })) {
  		return fail("precondition failed in H at %d; \\A r \\in {1, 2} : r = 1\n\nlhs: set(integer(1), integer(2))\n\n= %+v\n\nrhs: \"<func>\"\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, set(integer(1), integer(2)), "<func>", prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckH1(trace_i int, prev Event, this Event) error {
  
  	// \A s \in {1, 2} : \A r \in {3, 4} : r = s
  	if IsFalse(BoundedForall(set(integer(1), integer(2)), func(v1_s TLA) Bool {
  		return BoundedForall(set(integer(3), integer(4)), func(v2_r TLA) Bool { return Eq(v2_r, v1_s) })
  	})) {
  		return fail("precondition failed in H1 at %d; \\A s \\in {1, 2} : \\A r \\in {3, 4} : r = s\n\nlhs: set(integer(1), integer(2))\n\n= %+v\n\nrhs: \"<func>\"\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, set(integer(1), integer(2)), "<func>", prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckH2(trace_i int, prev Event, this Event) error {
  
  	// [ r \in RM |-> "a" ]["a"] = 1
  	if IsFalse(Eq(IndexInto(FnConstruct(set(str("s1"), str("2")), func(_ TLA) TLA { return str("a") }), str("a")), integer(1))) {
  		return fail("precondition failed in H2 at %d; [ r \\in RM |-> \"a\" ][\"a\"] = 1\n\nlhs: IndexInto(FnConstruct(set(str(\"s1\"), str(\"2\")), func(_ TLA) TLA { return str(\"a\") }), str(\"a\"))\n\n= %+v\n\nrhs: integer(1)\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, IndexInto(FnConstruct(set(str("s1"), str("2")), func(_ TLA) TLA { return str("a") }), str("a")), integer(1), prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckH3(trace_i int, prev Event, this Event) error {
  
  	// [ r \in RM |-> r ]["a"] = 1
  	if IsFalse(Eq(IndexInto(FnConstruct(set(str("s1"), str("2")), func(v4 TLA) TLA { return any(v4).(Set) }), str("a")), integer(1))) {
  		return fail("precondition failed in H3 at %d; [ r \\in RM |-> r ][\"a\"] = 1\n\nlhs: IndexInto(FnConstruct(set(str(\"s1\"), str(\"2\")), func(v4 TLA) TLA { return any(v4).(Set) }), str(\"a\"))\n\n= %+v\n\nrhs: integer(1)\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, IndexInto(FnConstruct(set(str("s1"), str("2")), func(v4 TLA) TLA { return any(v4).(Set) }), str("a")), integer(1), prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckH4(trace_i int, prev Event, this Event) error {
  
  	if IsFalse(BoundedForall(set(integer(1), integer(2)), func(v5_r TLA) Bool { return Eq(v5_r, integer(1)) })) {
  
  		// (\A r \in {1, 2} : r = 1 \/ \A r \in {2, 3} : r = 2)
  		if IsFalse(BoundedForall(set(integer(2), integer(3)), func(v6_r TLA) Bool { return Eq(v6_r, integer(2)) })) {
  			return fail("precondition failed in H4 at %d; (\\A r \\in {1, 2} : r = 1 \\/ \\A r \\in {2, 3} : r = 2)\n\nlhs: set(integer(2), integer(3))\n\n= %+v\n\nrhs: \"<func>\"\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, set(integer(2), integer(3)), "<func>", prev, this)
  		}
  	}
  
  	return nil
  }
  
  /* Action I cannot be translated because of: ToTrace(CounterExample) */
  
  func (monitor *Monitor) Checka(trace_i int, prev Event, this Event) error {
  
  	// 1
  	if IsFalse(integer(1)) {
  		return fail("check failed in a at %d; 1\n\nlhs: \"<none>\"\n\n= %+v\n\nrhs: \"<none>\"\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, "<none>", "<none>", prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) Checkb(trace_i int, prev Event, this Event) error {
  
  	// 1
  	if IsFalse(integer(1)) {
  		return fail("check failed in b at %d; 1\n\nlhs: \"<none>\"\n\n= %+v\n\nrhs: \"<none>\"\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, "<none>", "<none>", prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) Checkc(trace_i int, prev Event, this Event) error {
  
  	// 1
  	if IsFalse(integer(1)) {
  		return fail("check failed in c at %d; 1\n\nlhs: \"<none>\"\n\n= %+v\n\nrhs: \"<none>\"\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, "<none>", "<none>", prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckI1(trace_i int, prev Event, this Event) error {
  
  	var a TLA = integer(1)
  	var b TLA = integer(1)
  	var c TLA = integer(1)
  	// a + b + c = 1
  	if IsFalse(Eq(IntPlus(IntPlus(any(a).(Int), any(b).(Int)), any(c).(Int)), integer(1))) {
  		return fail("precondition failed in I1 at %d; a + b + c = 1\n\nlhs: IntPlus(IntPlus(any(a).(Int), any(b).(Int)), any(c).(Int))\n\n= %+v\n\nrhs: integer(1)\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, IntPlus(IntPlus(any(a).(Int), any(b).(Int)), any(c).(Int)), integer(1), prev, this)
  	}
  	return nil
  }
  
  func (monitor *Monitor) CheckSets(trace_i int, prev Event, this Event) error {
  
  	// {1, 2} \union {3} = {}
  	if IsFalse(Eq(SetUnion(set(integer(1), integer(2)), set(integer(3))), set())) {
  		return fail("precondition failed in Sets at %d; {1, 2} \\union {3} = {}\n\nlhs: SetUnion(set(integer(1), integer(2)), set(integer(3)))\n\n= %+v\n\nrhs: set()\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, SetUnion(set(integer(1), integer(2)), set(integer(3))), set(), prev, this)
  	}
  
  	// 1 \notin {3}
  	if IsFalse(SetNotIn(integer(1), set(integer(3)))) {
  		return fail("precondition failed in Sets at %d; 1 \\notin {3}\n\nlhs: integer(1)\n\n= %+v\n\nrhs: set(integer(3))\n\n= %+v\n\nprev: %+v\n\nthis: %+v", trace_i, integer(1), set(integer(3)), prev, this)
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
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar tlc2.TLC -monitor Counter.tla
  653 lines
  parse ok
  compile ok

  $ monitor_check TwoPhaseCommitFull
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar tlc2.TLC -monitor TwoPhaseCommitFull.tla
  1261 lines
  parse ok
  compile ok

  $ monitor_check raft
  ++ java -XX:+UseParallelGC -cp ../tlatools/org.lamport.tlatools/dist/tla2tools.jar tlc2.TLC -monitor raft.tla
  1762 lines
  parse ok
  compile ok
