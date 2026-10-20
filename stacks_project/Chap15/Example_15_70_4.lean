/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.DualNumber.Periodic.Injective
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/-!
# Example 15.70.4: a periodic injective resolution over the dual numbers

The reusable construction is owned by `DualNumber.Periodic`.  A chain complex indexed by `ℕ`
represents the source's cohomological complex supported in degrees `≤ 0`; the former bi-infinite
model was acyclic and therefore could not represent the residue module.

@stack 0A5U
-/

/- Example 15.70.4, tag `0A5U` (1): over a field, the augmentation from the left-infinite
`ε`-periodic dual-number complex to the residue module is a quasi-isomorphism. -/
@[stacks 0A5U "(1)"]
#check fun (k : Type u) [Field k] =>
  (inferInstance : QuasiIso (DualNumber.Periodic.augmentation k))

/- Example 15.70.4, tag `0A5U` (2): over a field, every term of this periodic representative is
injective. -/
@[stacks 0A5U "(2)"]
#check fun (k : Type u) [Field k] (n : ℕ) =>
  (inferInstance : Injective ((DualNumber.Periodic.complex k).X n))

/- The underlying source-facing complex is explicit and reuses Mathlib's alternating-constant
complex. -/
#check @DualNumber.Periodic.complex

/- Its augmentation is an explicit chain map whose degree-zero component is the residue quotient. -/
#check @DualNumber.Periodic.augmentation
#check @DualNumber.Periodic.augmentation_f_zero

/- The field-specific reusable owners are named instances, so downstream statements need no
proof-local instance reconstruction. -/
#check @DualNumber.regularInjective
#check @DualNumber.Periodic.termInjective
