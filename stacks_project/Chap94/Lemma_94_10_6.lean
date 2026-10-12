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
# Base change of representable morphisms having a morphism property

A property `P` as in Definition 94.10.1 is stable under 2-fibre-product
base change of 1-morphisms of groupoid fibrations over `(Sch/S)_fppf`
that are representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 94.10.6: let `S` be a scheme in `Sch_fppf`. Let `X`, `Y`, `Z` be
categories fibred in groupoids over `(Sch/S)_fppf`. Let `P` be a property of
morphisms of algebraic spaces as in Definition 94.10.1. Let `f : X ⟶ Y` be a
1-morphism representable by algebraic spaces, and let `g : Z ⟶ Y` be any
1-morphism. In the 2-fibre-product square of `(g, f)`, the base change is
`f' := TwoFibreProduct.fst g f : Z ×_Y X ⟶ Z` and the other projection is
`g' := TwoFibreProduct.snd g f`. If `f` has `P`, then `f'` has `P`.
Representability of `f'` is `relativelyRepresentableByAlgebraicSpaces.pullback_fst`
(Lemma 94.9.7). -/
@[stacks 045C]
theorem has.pullback_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f)
    (hP : has P f) :
    has P (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f) := sorry

end AlgebraicGeometry.Groupoids.Hom
