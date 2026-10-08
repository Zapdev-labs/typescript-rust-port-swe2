// Go oracle for the M3 corpus gate: same JSONL shape as rust/tools/parsecorpus.
// Usage: go run ./internal/parsecorpus <root>... > out.jsonl
package main

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sort"

	"github.com/microsoft/TypeScript/tsc/internal/ast"
	"github.com/microsoft/TypeScript/tsc/internal/core"
	"github.com/microsoft/TypeScript/tsc/internal/parser"
	"github.com/microsoft/TypeScript/tsc/internal/tspath"
)

type diag struct {
	Code int32    `json:"code"`
	Pos  int      `json:"pos"`
	End  int      `json:"end"`
	Cat  int      `json:"cat"`
	Key  string   `json:"key"`
	Args []string `json:"args"`
}

func parseOne(path string) (out map[string]any) {
	defer func() {
		if r := recover(); r != nil {
			out = map[string]any{"file": path, "panic": fmt.Sprint(r)}
		}
	}()
	text, err := os.ReadFile(path)
	if err != nil {
		return map[string]any{"file": path, "read_error": err.Error()}
	}
	fn := tspath.RootedFilePath(path)
	opts := ast.SourceFileParseOptions{
		FileName: fn,
		PathKey:  tspath.PathKey(path),
	}
	file := parser.ParseSourceFile(opts, string(text), core.GetScriptKindFromFileName(fn))
	var diags []diag
	for _, d := range append(file.Diagnostics(), file.JSDiagnostics()...) {
		args := d.MessageArgs()
		if args == nil {
			args = []string{}
		}
		diags = append(diags, diag{d.Code(), d.Pos(), d.End(), int(d.Category()), string(d.MessageKey()), args})
	}
	if diags == nil {
		diags = []diag{}
	}
	return map[string]any{"file": path, "diags": diags}
}

func main() {
	var files []string
	for _, root := range os.Args[1:] {
		filepath.WalkDir(root, func(p string, d os.DirEntry, err error) error {
			if err != nil || d.IsDir() {
				return nil
			}
			switch filepath.Ext(p) {
			case ".ts", ".tsx", ".mts", ".cts", ".js", ".jsx", ".mjs", ".cjs", ".json":
				files = append(files, p)
			}
			return nil
		})
	}
	sort.Strings(files)
	for _, f := range files {
		b, _ := json.Marshal(parseOne(f))
		fmt.Println(string(b))
	}
}
