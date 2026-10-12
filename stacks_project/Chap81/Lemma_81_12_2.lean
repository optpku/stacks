/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import stacks_project.Chap81.Lemma_81_12_2_Affine

/-!
# Lemma 81.12.2

For a Beauville–Laszlo glueing pair, the canonical functor
`Over (space R) ⥤ category R' f` restricts to an equivalence between affine
glueable algebraic spaces over `X` and affine objects of
`Spaces(U ← U' → X')`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

/-- Lemma 81.12.2: let `(algebraMap R R', f)` be a glueing pair. The functor
`functor R' f` restricts to an equivalence between the category of affine
algebraic spaces `Y` over `X` which are glueable for the pair and the full
subcategory of objects `(V, V', Y')` of `category R' f` with `V`, `V'`, and
`Y'` affine. -/
@[stacks 0F9Q, instance]
instance affineGlueableFunctor_isEquivalence {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f] :
    (affineGlueableFunctor R' f).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing
