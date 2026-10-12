/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.BaseChange
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Finiteness
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Flat
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Pushout
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Tail
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Tail.BaseChange
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Reindex
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Reindex.BaseChange

/-!
# Directed module-system API

This aggregate exposes the neutral module-system owner, its source-faithful
limit-finiteness, flatness, and source-base-change theorems, and the
generic tail and reindex APIs.  The finite-type specialization remains in the
separate `ModuleSystem.Specialization` leaf, so this import boundary stays
neutral.  The parent `Approximation` aggregate intentionally does not import
this file because the core module-system leaf itself depends on the parent ring
approximation owner.
-/

@[expose] public section
