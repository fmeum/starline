package main

import (
	"fmt"
	"math"
	"strconv"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

// evaluator holds state for the partial evaluation pass.
type evaluator struct {
	opts        *syntax.FileOptions
	thread      *starlark.Thread
	knownValues map[string]starlark.Value
	opaqueNames map[string]struct{}
}

func newEvaluator(opts *syntax.FileOptions) *evaluator {
	return &evaluator{
		opts:        opts,
		thread:      &starlark.Thread{Name: "pe"},
		knownValues: make(map[string]starlark.Value),
		opaqueNames: make(map[string]struct{}),
	}
}

// transformFile walks the file statements and returns a new *syntax.File
// with expressions partially evaluated.
func (ev *evaluator) transformFile(f *syntax.File) *syntax.File {
	var newStmts []syntax.Stmt
	for _, stmt := range f.Stmts {
		newStmts = append(newStmts, ev.transformStmt(stmt)...)
	}
	newStmts = pruneUnusedTopLevelConstants(newStmts)
	return &syntax.File{
		Path:  f.Path,
		Stmts: newStmts,
	}
}

// pruneUnusedTopLevelConstants removes dead top-level constant assignments after
// partial evaluation. Top-level expression statements are always preserved.
func pruneUnusedTopLevelConstants(stmts []syntax.Stmt) []syntax.Stmt {
	keep := make([]bool, len(stmts))
	live := make(map[string]struct{})

	// Backward liveness over top-level statements.
	for i := len(stmts) - 1; i >= 0; i-- {
		stmt := stmts[i]
		if name, ok := constantAssignName(stmt); ok {
			if _, needed := live[name]; !needed {
				continue
			}
		}

		keep[i] = true

		for name := range stmtDefinedNames(stmt) {
			delete(live, name)
		}
		for name := range stmtUsedNames(stmt) {
			live[name] = struct{}{}
		}
	}

	var out []syntax.Stmt
	for i, stmt := range stmts {
		if keep[i] {
			out = append(out, stmt)
		}
	}
	return out
}

func constantAssignName(stmt syntax.Stmt) (string, bool) {
	assign, ok := stmt.(*syntax.AssignStmt)
	if !ok || assign.Op != syntax.EQ {
		return "", false
	}
	lhs, ok := assign.LHS.(*syntax.Ident)
	if !ok {
		return "", false
	}
	if !isConstantExpr(assign.RHS) {
		return "", false
	}
	return lhs.Name, true
}

func isConstantExpr(expr syntax.Expr) bool {
	switch e := expr.(type) {
	case *syntax.Literal:
		return true
	case *syntax.Ident:
		return e.Name == "True" || e.Name == "False" || e.Name == "None"
	case *syntax.UnaryExpr:
		return isConstantExpr(e.X)
	case *syntax.ListExpr:
		for _, item := range e.List {
			if !isConstantExpr(item) {
				return false
			}
		}
		return true
	case *syntax.TupleExpr:
		for _, item := range e.List {
			if !isConstantExpr(item) {
				return false
			}
		}
		return true
	case *syntax.DictExpr:
		for _, item := range e.List {
			entry, ok := item.(*syntax.DictEntry)
			if !ok || !isConstantExpr(entry.Key) || !isConstantExpr(entry.Value) {
				return false
			}
		}
		return true
	case *syntax.ParenExpr:
		return isConstantExpr(e.X)
	default:
		return false
	}
}

func stmtUsedNames(stmt syntax.Stmt) map[string]struct{} {
	used := make(map[string]struct{})
	switch s := stmt.(type) {
	case *syntax.LoadStmt:
		// no uses
	case *syntax.AssignStmt:
		addExprUses(used, s.RHS)
		if s.Op != syntax.EQ {
			addExprUses(used, s.LHS)
		}
	case *syntax.ExprStmt:
		addExprUses(used, s.X)
	case *syntax.ReturnStmt:
		addExprUses(used, s.Result)
	case *syntax.ForStmt:
		addExprUses(used, s.X)
		for _, bodyStmt := range s.Body {
			mergeNameSet(used, stmtUsedNames(bodyStmt))
		}
	case *syntax.WhileStmt:
		addExprUses(used, s.Cond)
		for _, bodyStmt := range s.Body {
			mergeNameSet(used, stmtUsedNames(bodyStmt))
		}
	case *syntax.IfStmt:
		addExprUses(used, s.Cond)
		for _, bodyStmt := range s.True {
			mergeNameSet(used, stmtUsedNames(bodyStmt))
		}
		for _, bodyStmt := range s.False {
			mergeNameSet(used, stmtUsedNames(bodyStmt))
		}
	case *syntax.DefStmt:
		for _, param := range s.Params {
			if be, ok := param.(*syntax.BinaryExpr); ok && be.Op == syntax.EQ {
				addExprUses(used, be.Y)
			}
		}
		for _, bodyStmt := range s.Body {
			mergeNameSet(used, stmtUsedNames(bodyStmt))
		}
	default:
		// Be conservative for unsupported statements.
		syntax.Walk(s, func(n syntax.Node) bool {
			if id, ok := n.(*syntax.Ident); ok {
				used[id.Name] = struct{}{}
			}
			return true
		})
	}
	return used
}

func stmtDefinedNames(stmt syntax.Stmt) map[string]struct{} {
	defs := make(map[string]struct{})
	switch s := stmt.(type) {
	case *syntax.AssignStmt:
		collectIdents(s.LHS, defs)
	case *syntax.LoadStmt:
		for _, ident := range s.To {
			defs[ident.Name] = struct{}{}
		}
	case *syntax.DefStmt:
		defs[s.Name.Name] = struct{}{}
	case *syntax.ForStmt:
		collectIdents(s.Vars, defs)
	}
	return defs
}

func addExprUses(dst map[string]struct{}, expr syntax.Expr) {
	if expr == nil {
		return
	}
	freeVars := collectFreeVars(expr, nil)
	if freeVars.unknown {
		syntax.Walk(expr, func(n syntax.Node) bool {
			if id, ok := n.(*syntax.Ident); ok {
				dst[id.Name] = struct{}{}
			}
			return true
		})
		return
	}
	for name := range freeVars.names {
		dst[name] = struct{}{}
	}
}

func mergeNameSet(dst, src map[string]struct{}) {
	for name := range src {
		dst[name] = struct{}{}
	}
}

func (ev *evaluator) markOpaque(expr syntax.Expr) {
	switch e := expr.(type) {
	case *syntax.Ident:
		ev.opaqueNames[e.Name] = struct{}{}
	case *syntax.TupleExpr:
		for _, item := range e.List {
			ev.markOpaque(item)
		}
	case *syntax.ListExpr:
		for _, item := range e.List {
			ev.markOpaque(item)
		}
	}
}

func (ev *evaluator) transformStmt(stmt syntax.Stmt) []syntax.Stmt {
	switch s := stmt.(type) {
	case *syntax.LoadStmt:
		// Mark all imported names as opaque.
		for _, ident := range s.To {
			ev.opaqueNames[ident.Name] = struct{}{}
		}
		return []syntax.Stmt{s}

	case *syntax.AssignStmt:
		if s.Op == syntax.EQ {
			if lhs, ok := s.LHS.(*syntax.Ident); ok {
				newRHS := ev.transformExpr(s.RHS)
				if val, ok := ev.tryEval(newRHS); ok {
					ev.knownValues[lhs.Name] = val
					return []syntax.Stmt{&syntax.AssignStmt{
						OpPos: s.OpPos,
						Op:    s.Op,
						LHS:   s.LHS,
						RHS:   maybeMultiLine(valueToSyntaxExpr(val), s.RHS),
					}}
				}
				delete(ev.knownValues, lhs.Name)
				ev.opaqueNames[lhs.Name] = struct{}{}
				return []syntax.Stmt{&syntax.AssignStmt{
					OpPos: s.OpPos,
					Op:    s.Op,
					LHS:   s.LHS,
					RHS:   newRHS,
				}}
			}
		}
		// Augmented assignment or tuple LHS: mark all LHS idents opaque.
		ev.markOpaque(s.LHS)
		newRHS := ev.transformExpr(s.RHS)
		return []syntax.Stmt{&syntax.AssignStmt{
			OpPos: s.OpPos,
			Op:    s.Op,
			LHS:   s.LHS,
			RHS:   newRHS,
		}}

	case *syntax.DefStmt:
		ev.opaqueNames[s.Name.Name] = struct{}{}
		return []syntax.Stmt{s}

	case *syntax.ExprStmt:
		// Try to unroll top-level list/dict comprehensions.
		if comp, ok := s.X.(*syntax.Comprehension); ok {
			if exprs, ok := ev.tryUnrollComprehension(comp); ok {
				stmts := make([]syntax.Stmt, len(exprs))
				for i, expr := range exprs {
					stmts[i] = &syntax.ExprStmt{X: expr}
				}
				return stmts
			}
		}
		return []syntax.Stmt{&syntax.ExprStmt{X: ev.transformExpr(s.X)}}

	case *syntax.ReturnStmt:
		if s.Result == nil {
			return []syntax.Stmt{s}
		}
		return []syntax.Stmt{&syntax.ReturnStmt{Return: s.Return, Result: ev.transformExpr(s.Result)}}

	case *syntax.ForStmt, *syntax.IfStmt, *syntax.BranchStmt:
		return []syntax.Stmt{s}

	default:
		return []syntax.Stmt{s}
	}
}

// transformExpr builds a new expression with children transformed, then tries
// to evaluate it. Each physical node is passed to EvalExprOptions at most once.
func (ev *evaluator) transformExpr(expr syntax.Expr) syntax.Expr {
	if expr == nil {
		return nil
	}
	switch e := expr.(type) {
	case *syntax.Ident:
		if val, ok := ev.knownValues[e.Name]; ok {
			if s := valueToSyntaxExpr(val); s != nil {
				return s
			}
		}
		return e

	case *syntax.Literal:
		return e

	case *syntax.BinaryExpr:
		newX := ev.transformExpr(e.X)
		newY := ev.transformExpr(e.Y)
		newE := &syntax.BinaryExpr{Op: e.Op, OpPos: e.OpPos, X: newX, Y: newY}
		if val, ok := ev.tryEval(newE); ok {
			if s := valueToSyntaxExpr(val); s != nil {
				return maybeMultiLine(s, e)
			}
		}
		return newE

	case *syntax.UnaryExpr:
		newX := ev.transformExpr(e.X)
		newE := &syntax.UnaryExpr{Op: e.Op, OpPos: e.OpPos, X: newX}
		if val, ok := ev.tryEval(newE); ok {
			if s := valueToSyntaxExpr(val); s != nil {
				return maybeMultiLine(s, e)
			}
		}
		return newE

	case *syntax.ListExpr:
		newList := make([]syntax.Expr, len(e.List))
		for i, item := range e.List {
			newList[i] = ev.transformExpr(item)
		}
		newE := &syntax.ListExpr{Lbrack: e.Lbrack, Rbrack: e.Rbrack, List: newList}
		if val, ok := ev.tryEval(newE); ok {
			if s := valueToSyntaxExpr(val); s != nil {
				return maybeMultiLine(s, e)
			}
		}
		return newE

	case *syntax.TupleExpr:
		newList := make([]syntax.Expr, len(e.List))
		for i, item := range e.List {
			newList[i] = ev.transformExpr(item)
		}
		newE := &syntax.TupleExpr{Lparen: e.Lparen, Rparen: e.Rparen, List: newList}
		if val, ok := ev.tryEval(newE); ok {
			if s := valueToSyntaxExpr(val); s != nil {
				return maybeMultiLine(s, e)
			}
		}
		return newE

	case *syntax.DictExpr:
		newList := make([]syntax.Expr, len(e.List))
		for i, item := range e.List {
			entry := item.(*syntax.DictEntry)
			newList[i] = &syntax.DictEntry{
				Key:   ev.transformExpr(entry.Key),
				Value: ev.transformExpr(entry.Value),
			}
		}
		newE := &syntax.DictExpr{Lbrace: e.Lbrace, Rbrace: e.Rbrace, List: newList}
		if val, ok := ev.tryEval(newE); ok {
			if s := valueToSyntaxExpr(val); s != nil {
				return maybeMultiLine(s, e)
			}
		}
		return newE

	case *syntax.CallExpr:
		// Transform args (substitute known values), but don't evaluate the call.
		newArgs := make([]syntax.Expr, len(e.Args))
		for i, arg := range e.Args {
			newArgs[i] = ev.transformCallArg(arg)
		}
		return &syntax.CallExpr{
			Fn:     e.Fn,
			Lparen: e.Lparen,
			Args:   newArgs,
			Rparen: e.Rparen,
		}

	case *syntax.CondExpr:
		newCond := ev.transformExpr(e.Cond)
		newTrue := ev.transformExpr(e.True)
		newFalse := ev.transformExpr(e.False)
		// Short-circuit on known boolean condition.
		if ident, ok := newCond.(*syntax.Ident); ok {
			switch ident.Name {
			case "True":
				return newTrue
			case "False":
				return newFalse
			}
		}
		newE := &syntax.CondExpr{If: e.If, Cond: newCond, True: newTrue, ElsePos: e.ElsePos, False: newFalse}
		if val, ok := ev.tryEval(newE); ok {
			if s := valueToSyntaxExpr(val); s != nil {
				return maybeMultiLine(s, e)
			}
		}
		return newE

	case *syntax.ParenExpr:
		newX := ev.transformExpr(e.X)
		newE := &syntax.ParenExpr{Lparen: e.Lparen, Rparen: e.Rparen, X: newX}
		if val, ok := ev.tryEval(newE); ok {
			if s := valueToSyntaxExpr(val); s != nil {
				return maybeMultiLine(s, e)
			}
		}
		return newE

	case *syntax.DotExpr:
		newX := ev.transformExpr(e.X)
		return &syntax.DotExpr{X: newX, Dot: e.Dot, Name: e.Name, NamePos: e.NamePos}

	case *syntax.IndexExpr:
		newX := ev.transformExpr(e.X)
		newY := ev.transformExpr(e.Y)
		newE := &syntax.IndexExpr{X: newX, Lbrack: e.Lbrack, Y: newY, Rbrack: e.Rbrack}
		if val, ok := ev.tryEval(newE); ok {
			if s := valueToSyntaxExpr(val); s != nil {
				return maybeMultiLine(s, e)
			}
		}
		return newE

	case *syntax.Comprehension:
		result := ev.transformComprehension(e)
		return maybeMultiLine(result, e)

	case *syntax.LambdaExpr:
		return e

	default:
		return e
	}
}

// transformCallArg transforms a call argument, being careful about keyword args
// (BinaryExpr with Op == EQ, where the LHS is the keyword name).
func (ev *evaluator) transformCallArg(arg syntax.Expr) syntax.Expr {
	if be, ok := arg.(*syntax.BinaryExpr); ok && be.Op == syntax.EQ {
		// Keyword argument: LHS is the keyword name (not a variable), transform only RHS.
		newRHS := ev.transformExpr(be.Y)
		// Stamp the original RHS start position onto the new RHS so that
		// convertast doesn't think there's a line break between "name =" and the value.
		origStart, _ := be.Y.Span()
		newRHS = repositionStart(newRHS, origStart)
		return &syntax.BinaryExpr{Op: be.Op, OpPos: be.OpPos, X: be.X, Y: newRHS}
	}
	return ev.transformExpr(arg)
}

// repositionStart stamps pos as the start position of a (possibly synthetic) expression.
// This is needed so that convertast computes correct LineBreak values.
func repositionStart(expr syntax.Expr, pos syntax.Position) syntax.Expr {
	if !pos.IsValid() {
		return expr
	}
	switch e := expr.(type) {
	case *syntax.Ident:
		e.NamePos = pos
	case *syntax.Literal:
		e.TokenPos = pos
	case *syntax.UnaryExpr:
		e.OpPos = pos
	case *syntax.ListExpr:
		e.Lbrack = pos
	case *syntax.TupleExpr:
		e.Lparen = pos
	case *syntax.DictExpr:
		e.Lbrace = pos
	}
	return expr
}

// maybeMultiLine adjusts the bracket positions of a synthetic list/dict/tuple
// to be multi-line if the original expression was multi-line.
// This ensures ForceMultiLine is set correctly in convertast.
func maybeMultiLine(newExpr, origExpr syntax.Expr) syntax.Expr {
	if newExpr == nil || origExpr == nil {
		return newExpr
	}
	origStart, origEnd := origExpr.Span()
	if origStart.Line == origEnd.Line || !origStart.IsValid() || !origEnd.IsValid() {
		return newExpr
	}
	// Original was multi-line: stamp different line positions onto the synthetic node.
	switch e := newExpr.(type) {
	case *syntax.ListExpr:
		e.Lbrack = origStart
		e.Rbrack = origEnd
	case *syntax.DictExpr:
		e.Lbrace = origStart
		e.Rbrace = origEnd
	case *syntax.TupleExpr:
		e.Lparen = origStart
		e.Rparen = origEnd
	}
	return newExpr
}

// transformComprehension handles list/dict comprehensions.
func (ev *evaluator) transformComprehension(e *syntax.Comprehension) syntax.Expr {
	// Collect names bound by ForClause.Vars.
	boundNames := make(map[string]struct{})
	for _, clause := range e.Clauses {
		if fc, ok := clause.(*syntax.ForClause); ok {
			collectIdents(fc.Vars, boundNames)
		}
	}

	// Collect free variables in body and clause exprs (excluding bound names).
	freeVars := collectFreeVars(e, boundNames)
	if freeVars.unknown {
		return e
	}

	// If all free vars are known, try to evaluate the whole comprehension.
	allKnown := true
	for name := range freeVars.names {
		if _, opaque := ev.opaqueNames[name]; opaque {
			allKnown = false
			break
		}
		if _, known := ev.knownValues[name]; !known {
			if _, inUniverse := starlark.Universe[name]; !inUniverse {
				allKnown = false
				break
			}
		}
	}
	if allKnown {
		if val, ok := ev.tryEval(e); ok {
			if s := valueToSyntaxExpr(val); s != nil {
				return s
			}
		}
	}

	// Otherwise, transform the iterable exprs in ForClauses and IfClause conds.
	newClauses := make([]syntax.Node, len(e.Clauses))
	for i, clause := range e.Clauses {
		switch c := clause.(type) {
		case *syntax.ForClause:
			newClauses[i] = &syntax.ForClause{
				For:  c.For,
				Vars: c.Vars,
				In:   c.In,
				X:    ev.transformExpr(c.X),
			}
		case *syntax.IfClause:
			newClauses[i] = &syntax.IfClause{
				If:   c.If,
				Cond: ev.transformExpr(c.Cond),
			}
		default:
			newClauses[i] = clause
		}
	}
	return &syntax.Comprehension{
		Curly:   e.Curly,
		Lbrack:  e.Lbrack,
		Body:    e.Body,
		Clauses: newClauses,
		Rbrack:  e.Rbrack,
	}
}

// ---------------------------------------------------------------------------
// Comprehension unrolling
// ---------------------------------------------------------------------------

// savedBinding preserves the state of one variable before temporarily overriding it.
type savedBinding struct {
	name   string
	had    bool
	val    starlark.Value
	opaque bool
}

func (ev *evaluator) bindVar(name string, val starlark.Value) savedBinding {
	saved := savedBinding{name: name}
	saved.val, saved.had = ev.knownValues[name]
	_, saved.opaque = ev.opaqueNames[name]
	ev.knownValues[name] = val
	delete(ev.opaqueNames, name)
	return saved
}

func (ev *evaluator) restoreBinding(saved savedBinding) {
	if saved.had {
		ev.knownValues[saved.name] = saved.val
	} else {
		delete(ev.knownValues, saved.name)
	}
	if saved.opaque {
		ev.opaqueNames[saved.name] = struct{}{}
	} else {
		delete(ev.opaqueNames, saved.name)
	}
}

func (ev *evaluator) restoreBindings(saved []savedBinding) {
	for i := len(saved) - 1; i >= 0; i-- {
		ev.restoreBinding(saved[i])
	}
}

// bindVars binds the pattern vars to val, supporting simple idents and tuples.
func (ev *evaluator) bindVars(vars syntax.Expr, val starlark.Value) ([]savedBinding, bool) {
	switch v := vars.(type) {
	case *syntax.Ident:
		return []savedBinding{ev.bindVar(v.Name, val)}, true
	case *syntax.TupleExpr:
		tup, ok := val.(starlark.Tuple)
		if !ok || len(tup) != len(v.List) {
			return nil, false
		}
		var saved []savedBinding
		for i, nameExpr := range v.List {
			s, ok := ev.bindVars(nameExpr, tup[i])
			if !ok {
				ev.restoreBindings(saved)
				return nil, false
			}
			saved = append(saved, s...)
		}
		return saved, true
	default:
		return nil, false
	}
}

// tryUnrollComprehension attempts to unroll a comprehension into individual
// expressions. Returns the list of body expressions and true if successful.
func (ev *evaluator) tryUnrollComprehension(comp *syntax.Comprehension) ([]syntax.Expr, bool) {
	var results []syntax.Expr
	if !ev.unrollClauses(comp.Clauses, comp.Body, &results) {
		return nil, false
	}
	return results, true
}

func (ev *evaluator) unrollClauses(clauses []syntax.Node, body syntax.Expr, results *[]syntax.Expr) bool {
	if len(clauses) == 0 {
		transformed := ev.transformExpr(body)
		*results = append(*results, transformed)
		return true
	}

	switch c := clauses[0].(type) {
	case *syntax.ForClause:
		// Evaluate the iterable directly (it must be fully known).
		val, ok := ev.tryEval(c.X)
		if !ok {
			return false
		}
		iter, ok := val.(starlark.Iterable)
		if !ok {
			return false
		}
		it := iter.Iterate()
		defer it.Done()
		var elem starlark.Value
		for it.Next(&elem) {
			saved, ok := ev.bindVars(c.Vars, elem)
			if !ok {
				return false
			}
			if !ev.unrollClauses(clauses[1:], body, results) {
				ev.restoreBindings(saved)
				return false
			}
			ev.restoreBindings(saved)
		}
		return true

	case *syntax.IfClause:
		val, ok := ev.tryEval(c.Cond)
		if !ok {
			return false
		}
		if val.Truth() {
			return ev.unrollClauses(clauses[1:], body, results)
		}
		return true // condition false: skip this iteration
	}
	return false
}

// ---------------------------------------------------------------------------
// Free variable collection
// ---------------------------------------------------------------------------

// freeVarResult collects free variable names or signals unknown.
type freeVarResult struct {
	names   map[string]struct{}
	unknown bool
}

// collectFreeVars collects free variable names in expr, excluding boundNames.
func collectFreeVars(expr syntax.Expr, boundNames map[string]struct{}) freeVarResult {
	result := freeVarResult{names: make(map[string]struct{})}
	walkFreeVars(expr, boundNames, &result)
	return result
}

func walkFreeVars(expr syntax.Expr, boundNames map[string]struct{}, result *freeVarResult) {
	if result.unknown || expr == nil {
		return
	}
	switch e := expr.(type) {
	case *syntax.Ident:
		if _, bound := boundNames[e.Name]; !bound {
			result.names[e.Name] = struct{}{}
		}
	case *syntax.Literal:
		// no free vars
	case *syntax.BinaryExpr:
		walkFreeVars(e.X, boundNames, result)
		walkFreeVars(e.Y, boundNames, result)
	case *syntax.UnaryExpr:
		walkFreeVars(e.X, boundNames, result)
	case *syntax.ListExpr:
		for _, item := range e.List {
			walkFreeVars(item, boundNames, result)
		}
	case *syntax.TupleExpr:
		for _, item := range e.List {
			walkFreeVars(item, boundNames, result)
		}
	case *syntax.DictExpr:
		for _, item := range e.List {
			entry := item.(*syntax.DictEntry)
			walkFreeVars(entry.Key, boundNames, result)
			walkFreeVars(entry.Value, boundNames, result)
		}
	case *syntax.CallExpr:
		walkFreeVars(e.Fn, boundNames, result)
		for _, arg := range e.Args {
			if be, ok := arg.(*syntax.BinaryExpr); ok && be.Op == syntax.EQ {
				// Keyword arg: LHS is name (not free var), RHS is value.
				walkFreeVars(be.Y, boundNames, result)
			} else {
				walkFreeVars(arg, boundNames, result)
			}
		}
	case *syntax.DotExpr:
		walkFreeVars(e.X, boundNames, result)
		// e.Name is a field name, not a variable
	case *syntax.IndexExpr:
		walkFreeVars(e.X, boundNames, result)
		walkFreeVars(e.Y, boundNames, result)
	case *syntax.CondExpr:
		walkFreeVars(e.Cond, boundNames, result)
		walkFreeVars(e.True, boundNames, result)
		walkFreeVars(e.False, boundNames, result)
	case *syntax.ParenExpr:
		walkFreeVars(e.X, boundNames, result)
	case *syntax.Comprehension:
		// Nested comprehension: collect its own bound vars.
		innerBound := make(map[string]struct{})
		for name := range boundNames {
			innerBound[name] = struct{}{}
		}
		for _, clause := range e.Clauses {
			if fc, ok := clause.(*syntax.ForClause); ok {
				collectIdents(fc.Vars, innerBound)
			}
		}
		walkFreeVars(e.Body, innerBound, result)
		for _, clause := range e.Clauses {
			switch c := clause.(type) {
			case *syntax.ForClause:
				walkFreeVars(c.X, boundNames, result) // iterable uses outer scope
			case *syntax.IfClause:
				walkFreeVars(c.Cond, innerBound, result)
			}
		}
	case *syntax.LambdaExpr:
		result.unknown = true
	case *syntax.SliceExpr:
		walkFreeVars(e.X, boundNames, result)
		walkFreeVars(e.Lo, boundNames, result)
		walkFreeVars(e.Hi, boundNames, result)
		walkFreeVars(e.Step, boundNames, result)
	}
}

// collectIdents adds all ident names from expr into the set.
func collectIdents(expr syntax.Expr, set map[string]struct{}) {
	if expr == nil {
		return
	}
	switch e := expr.(type) {
	case *syntax.Ident:
		set[e.Name] = struct{}{}
	case *syntax.TupleExpr:
		for _, item := range e.List {
			collectIdents(item, set)
		}
	case *syntax.ListExpr:
		for _, item := range e.List {
			collectIdents(item, set)
		}
	case *syntax.ParenExpr:
		collectIdents(e.X, set)
	}
}

// tryEval attempts to evaluate expr using known values. Returns the value and
// true if successful, or (nil, false) otherwise.
func (ev *evaluator) tryEval(expr syntax.Expr) (starlark.Value, bool) {
	freeVars := collectFreeVars(expr, nil)
	if freeVars.unknown {
		return nil, false
	}

	// Build environment: check all free vars are resolvable.
	env := make(starlark.StringDict)
	for name := range freeVars.names {
		if _, opaque := ev.opaqueNames[name]; opaque {
			return nil, false
		}
		if val, ok := ev.knownValues[name]; ok {
			env[name] = val
		} else if _, inUniverse := starlark.Universe[name]; inUniverse {
			// Will be resolved from universe automatically.
		} else {
			return nil, false
		}
	}

	val, err := starlark.EvalExprOptions(ev.opts, ev.thread, expr, env)
	if err != nil {
		return nil, false
	}
	return val, true
}

// ---------------------------------------------------------------------------
// Value → syntax expression conversion
// ---------------------------------------------------------------------------

// dummyFile is used for creating valid positions for synthetic nodes.
var dummyFile = "<synthetic>"

// validPos is a valid dummy position for synthetic nodes.
var validPos = syntax.MakePosition(&dummyFile, 1, 1)

// valueToSyntaxExpr converts a Starlark value to a syntax expression.
// Returns nil if the value cannot be represented (Bytes, Function, Builtin, Set,
// too-large Int, non-finite Float).
func valueToSyntaxExpr(v starlark.Value) syntax.Expr {
	if v == nil {
		return nil
	}
	switch val := v.(type) {
	case starlark.NoneType:
		return &syntax.Ident{Name: "None", NamePos: validPos}

	case starlark.Bool:
		if val {
			return &syntax.Ident{Name: "True", NamePos: validPos}
		}
		return &syntax.Ident{Name: "False", NamePos: validPos}

	case starlark.String:
		s := string(val)
		raw := strconv.Quote(s)
		return &syntax.Literal{Token: syntax.STRING, Raw: raw, Value: s, TokenPos: validPos}

	case starlark.Int:
		i64, ok := val.Int64()
		if !ok {
			return nil
		}
		if i64 >= 0 {
			return &syntax.Literal{
				Token:    syntax.INT,
				Raw:      fmt.Sprintf("%d", i64),
				Value:    i64,
				TokenPos: validPos,
			}
		}
		absVal := -i64
		lit := &syntax.Literal{
			Token:    syntax.INT,
			Raw:      fmt.Sprintf("%d", absVal),
			Value:    absVal,
			TokenPos: validPos,
		}
		return &syntax.UnaryExpr{Op: syntax.MINUS, OpPos: validPos, X: lit}

	case starlark.Float:
		f := float64(val)
		if math.IsInf(f, 0) || math.IsNaN(f) {
			return nil
		}
		raw := formatFloat(f)
		if f >= 0 {
			return &syntax.Literal{Token: syntax.FLOAT, Raw: raw, Value: f, TokenPos: validPos}
		}
		absRaw := formatFloat(-f)
		lit := &syntax.Literal{Token: syntax.FLOAT, Raw: absRaw, Value: -f, TokenPos: validPos}
		return &syntax.UnaryExpr{Op: syntax.MINUS, OpPos: validPos, X: lit}

	case *starlark.List:
		items := make([]syntax.Expr, val.Len())
		for i := 0; i < val.Len(); i++ {
			s := valueToSyntaxExpr(val.Index(i))
			if s == nil {
				return nil
			}
			items[i] = s
		}
		return &syntax.ListExpr{List: items, Lbrack: validPos, Rbrack: validPos}

	case starlark.Tuple:
		items := make([]syntax.Expr, val.Len())
		for i := 0; i < val.Len(); i++ {
			s := valueToSyntaxExpr(val[i])
			if s == nil {
				return nil
			}
			items[i] = s
		}
		return &syntax.TupleExpr{List: items, Lparen: validPos, Rparen: validPos}

	case *starlark.Dict:
		items := val.Items()
		entries := make([]syntax.Expr, len(items))
		for i, kv := range items {
			k := valueToSyntaxExpr(kv[0])
			v2 := valueToSyntaxExpr(kv[1])
			if k == nil || v2 == nil {
				return nil
			}
			entries[i] = &syntax.DictEntry{Key: k, Value: v2}
		}
		return &syntax.DictExpr{List: entries, Lbrace: validPos, Rbrace: validPos}

	case starlark.Bytes, *starlark.Function, *starlark.Builtin, *starlark.Set:
		return nil

	default:
		return nil
	}
}

// formatFloat formats a float for use as a Starlark literal.
func formatFloat(f float64) string {
	s := strconv.FormatFloat(f, 'g', -1, 64)
	for _, c := range s {
		if c == '.' || c == 'e' || c == 'E' {
			return s
		}
	}
	return s + ".0"
}
