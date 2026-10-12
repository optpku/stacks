/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap80.Definition_80_4_1_Relative
public import stacks_project.Chap87.Definition_87_25_1_Surjective

/-!
# Reduction squares of smooth morphisms of formal algebraic spaces

A morphism of formal algebraic spaces representable by algebraic spaces and
smooth has cartesian reduction square: the identification
`reduction X` with the fibre product of `X` and `reduction Y` over `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 87.12.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S` which is representable by algebraic spaces
and smooth (for example étale). Then `reduction X` equals the fibre product
`X ×_Y reduction Y`, i.e. the square of `reductionι X`, `mapReduction f`,
`f`, and `reductionι Y` is cartesian. -/
@[stacks 0GB7]
theorem isPullback_reductionι {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] {f : X ⟶ Y}
    (hf : AlgebraicSpace.relativeAlgebraicSpaces (@AlgebraicSpace.Smooth S) f) :
    IsPullback (reductionι X) (mapReduction f) f (reductionι Y) :=
  sorry

/-- If `f` is representable by algebraic spaces and étale, then the reduction
square of `f` is cartesian. Étale morphisms of algebraic spaces are smooth, so
this is the parenthetical special case of `isPullback_reductionι`. -/
theorem isPullback_reductionι_of_etale {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] {f : X ⟶ Y}
    (hf : AlgebraicSpace.relativeAlgebraicSpaces (@AlgebraicSpace.Etale S) f) :
    IsPullback (reductionι X) (mapReduction f) f (reductionι Y) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
