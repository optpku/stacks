/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import stacks_project.Chap62.Remark_62_5_6_Support

/-!
# Equidimensional families of cycles on fibres

This file records the Stacks condition that the support of a family of
`r`-cycles on fibres is contained in a closed subscheme of relative
dimension at most `r`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/-- A family of `r`-cycles on fibres is equidimensional when its support is
contained in a closed subscheme of relative dimension at most `r`. -/
def Equidimensional {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    (α : CyclesOnFibers f r) : Prop :=
  ∃ W : X.IdealSheafData,
    support α ⊆ W.support ∧ RelativeDimensionLE (W.subschemeι ≫ f) r

/-- Equidimensionality means there is a closed subscheme containing the support
and of relative dimension at most `r`. -/
theorem equidimensional_iff {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    (α : CyclesOnFibers f r) :
    Equidimensional α ↔
      ∃ W : X.IdealSheafData,
        support α ⊆ W.support ∧ RelativeDimensionLE (W.subschemeι ≫ f) r :=
  sorry

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
