from go_lower import translate_go

source = """
package main

import "fmt"

type Daemon struct {
    Name string
}

func (d *Daemon) Start() {
    fmt.Println(d.Name)
}

func add(a int, b int) int {
    return a + b
}
"""

python_code = translate_go(source, import_paths=["/usr/local/go/src"])

exec(python_code, globals())

fmt.Println("printed here: %d" % add(2, 1))
