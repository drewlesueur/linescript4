# LineScript4

LineScript4 is a small stack based language implemented in [src/linescript4/linescript4.go](src/linescript4/linescript4.go).  The interpreter parses tokens separated by whitespace and uses a stack for evaluation.

This document gives a brief overview of the language features gathered from the Go implementation.  Only the interpreter file was inspected for this information.

## Basics

* **Comments** start with `#` and continue to the end of the line.
* **Strings** can be written in a few ways:
  * Prefix with `.` – e.g. `.foo`.
  * Quoted with `"` or `'`.
* **Numbers** are detected automatically.  Appending `f` creates a float (`1.0f`).
* A newline, semicolon (`;`) or comma (`,`) ends the current expression.
* Parentheses `()`, brackets `[]` and braces `{}` are used for grouping, arrays and objects respectively.

The language is stack based.  Most operations pop their arguments from the stack and push results back.

## Variables

Variables are stored in a record.  When assigning you pass the variable name as a string.  This allows dynamic assignment.

```text
let .x 10        # set variable x to 10
local .y 20      # set y only in the current scope
```

`def` defines a function and stores it under a name in the current scope:

```text
def .greet .name
    say "Hello " name cc
end

# Call it
greet "Alice"
```

The builtin `cc` concatenates two values.

## Arithmetic and Comparison

Built‑in operators exist for common math and comparisons.  Examples include `+`, `-`, `*`, `/`, `%`, `lt`, `gt`, `lte`, `gte`, `eq`, `neq` and more.  They pop arguments from the stack and push the result.

```text
say + 2 3        # prints 5
say times 4 5    # multiplication, also available as '*'
```

## Arrays and Objects

Arrays are created with `[` and `]` while objects use `{` and `}`:

```text
let .arr [1 2 3]
let .obj {"foo" 1 "bar" 2}
```

Useful functions include `push`, `pop`, `shift`, `unshift`, `slice`, `splice`, `length`, `keys`, `getProp` and `setProp`.

## Conditionals

Conditional execution is provided by `if`, optional `else if` and `else`, terminated by `end`:

```text
if eq x 10
    say "ten"
else if lt x 10
    say "less"
else
    say "more"
end
```

## Loops

The interpreter supports several looping constructs:

* `loop <n> <indexVar>` – run a fixed number of times.
* `loopRange <start> <end> <indexVar>` – inclusive numeric range.
* `each <collection> [indexVar itemVar]` – iterate over arrays or maps.
* `map`, `filter`, `sort` – helpers built on top of `each`.
* `forever` – infinite loop until `break`.

Example numeric loop:

```text
loop 5 .i
    say "i=" i
end
```

Iterating over an array:

```text
let .nums [1 2 3]
nums each .idx .val
    say idx ":" val
end
```

## Functions and Asynchronous Execution

Functions are first class values produced with `func` or `def`.  They capture lexical scope.  The `go` builtin runs a block in its own goroutine and `wait` waits on it.

```text
def .delayedSay .msg
    sleep 1000
    say msg
end

let .task go delayedSay "hi"
wait task
```

## Input/Output

`say` prints values.  `sayRaw` writes without formatting.  File and network helpers (`readFile`, `writeFile`, `tcpConnect`, etc.) are available as built‑ins.

## Running Code

The interpreter expects a file name as its argument:

```bash
$ go run . myscript.ls
```

Where `myscript.ls` contains linescript code as shown in the examples above.

## Notes

This language and its implementation are experimental.  Many features are driven directly by the interpreter in `linescript4.go`, so behaviour may change over time.
