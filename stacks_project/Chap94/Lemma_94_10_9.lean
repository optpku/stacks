/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Monotonicity of having a morphism property

If `P ≤ P'` as properties of morphisms of algebraic spaces in the sense of
Definition 94.10.1, then a 1-morphism representable by algebraic spaces that
has `P` also has `P'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 94.10.9: let `S` be a scheme in `Sch_fppf`. Let `X` and `Y` be
categories fibred in groupoids over `(Sch/S)_fppf`. Let `f : X ⟶ Y` be a
1-morphism representable by algebraic spaces. Let `P` and `P'` be properties
of morphisms of algebraic spaces as in Definition 94.10.1, so each is stable
under base change and fppf local on the target. If `P ≤ P'`, then `has P f`
implies `has P' f`. -/
@[stacks 045F]
theorem has.of_le {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {P P' : MorphismProperty (AlgebraicSpace S)}
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [P'.IsStableUnderBaseChange]
    [P'.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : P ≤ P') (hfP : has P f) : has P' f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
