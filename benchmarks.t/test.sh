#!/usr/bin/env bash

monitor_check() {
  set -e
  tlc -monitor $1.tla | make_det | sed -n "/MONITOR START/,/MONITOR END/p" > $1.go
  go build $1.go && echo compile ok
  gofmt $1.go || cat $1.go
}
