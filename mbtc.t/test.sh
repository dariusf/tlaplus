#!/usr/bin/env bash

# definitions for use in cram tests

monitor_check() {
  tlc -monitor $1.tla | make_det | sed -n "/MONITOR START/,/MONITOR END/p" > $1.go
  echo "$(wc -l < $1.go | tr -d ' ') lines"
  gofmt $1.go > /dev/null || { cat $1.go; return 1; }
  echo parse ok
  go build $1.go || { gofmt $1.go; return 1; }
  echo compile ok
}

monitor_check_show() {
  monitor_check "$@"
  gofmt $1.go || cat $1.go
}
