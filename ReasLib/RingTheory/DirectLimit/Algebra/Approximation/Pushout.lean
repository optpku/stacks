/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Pushout.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Pushout.FinitePresentation
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module.BaseChange
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Pushout
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Specialization
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushout API for directed algebra approximations

The lightweight ring-level owner is `Approximation.Pushout.Core`.
`Approximation.ModuleSystem.Pushout` supplies the generic source-side module
equivalence.  This aggregate intentionally adds no finite-module aliases: the
generic declarations are the canonical downstream API.
-/

@[expose] public section
