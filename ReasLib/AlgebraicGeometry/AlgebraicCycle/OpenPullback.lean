/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Restriction of algebraic cycles to open subschemes

This file defines coefficientwise restriction of integer algebraic cycles to open subschemes and
records its local-finiteness and coefficient formulas.
-/

@[expose] public section

open Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {X : Scheme.{u}}

/-- Restricting the coefficients of an algebraic cycle along an open immersion preserves locally
finite support. -/
theorem openPullback_locallyFiniteSupport (U : X.Opens) (α : AlgebraicCycle X ℤ) :
    LocallyFiniteSupport (fun u : U.toScheme ↦ α (U.ι u)) := sorry

/-- The algebraic cycle on an open subscheme obtained by restricting coefficients along its
canonical immersion. -/
noncomputable def openPullback (U : X.Opens) (α : AlgebraicCycle X ℤ) :
    AlgebraicCycle U.toScheme ℤ where
  toFun := fun u ↦ α (U.ι u)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun u _ ↦
    openPullback_locallyFiniteSupport U α u

/-- The coefficient of an open pullback is the coefficient at the corresponding point of the
ambient scheme. -/
theorem openPullback_apply (U : X.Opens) (α : AlgebraicCycle X ℤ) (u : U.toScheme) :
    openPullback U α u = α (U.ι u) := sorry

end AlgebraicGeometry.AlgebraicCycle
