package main

import (
	"fmt"
	"os"

	"github.com/bazelbuild/buildtools/build"
	"github.com/bazelbuild/buildtools/convertast"
	"go.starlark.net/syntax"
)

func main() {
	var filename string
	var src []byte
	var err error

	if len(os.Args) > 1 {
		filename = os.Args[1]
		src, err = os.ReadFile(filename)
		if err != nil {
			fmt.Fprintf(os.Stderr, "error reading %s: %v\n", filename, err)
			os.Exit(1)
		}
	} else {
		filename = "<stdin>"
		src, err = os.ReadFile("/dev/stdin")
		if err != nil {
			fmt.Fprintf(os.Stderr, "error reading stdin: %v\n", err)
			os.Exit(1)
		}
	}

	opts := &syntax.FileOptions{}
	f, err := opts.Parse(filename, src, syntax.RetainComments)
	if err != nil {
		fmt.Fprintf(os.Stderr, "parse error: %v\n", err)
		os.Exit(1)
	}

	ev := newEvaluator(opts)
	outFile := ev.transformFile(f)

	buildFile := convertast.ConvFile(outFile)
	buildFile.Type = build.TypeBuild
	formatted := build.Format(buildFile)
	os.Stdout.Write(formatted)
}
