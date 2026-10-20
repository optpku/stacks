/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-!
# The profinite integers

`hatZ` is the profinite completion of the infinite cyclic group, realised as the limit of its
finite quotients. This is the single owner of `Ẑ` in the library; finite-field Galois groups,
tame fundamental groups and degree extensions all use it.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace ProfiniteGrp

/-- The infinite cyclic group `ℤ`, written multiplicatively in universe `u`. -/
abbrev integerGroup : GrpCat.{u} :=
  GrpCat.of (Multiplicative (ULift.{u} ℤ))

/-- The profinite completion of the infinite cyclic group. -/
noncomputable abbrev hatZ : ProfiniteGrp.{u} :=
  ProfiniteCompletion.completion integerGroup.{u}

/-- The canonical image of `n : ℕ` in `hatZ`. -/
noncomputable def hatZNatCast (n : ℕ) : hatZ.{u} :=
  ProfiniteCompletion.etaFn integerGroup.{u} (Multiplicative.ofAdd (ULift.up (n : ℤ)))

/-- The canonical generator `1` in `hatZ`. -/
noncomputable def hatZOne : hatZ.{u} :=
  hatZNatCast 1

end ProfiniteGrp
