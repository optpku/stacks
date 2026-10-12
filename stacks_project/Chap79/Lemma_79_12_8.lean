/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap79.Lemma_79_12_8_OfPoint

/-!
# Étale criterion for the finite-part functor
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

/-- Lemma 79.12.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Suppose that `U` is a scheme, `U ⟶ Y` is an étale
morphism and `Z ⊂ U ×_Y X` is an open subspace finite over `U`. Then the
induced morphism `U ⟶ (X/Y)_fin` is étale. -/
@[stacks 04QE]
theorem hom_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U : Over S} (a : ofOver U ⟶ Y) [AlgebraicSpace.Etale a]
    (Z : OpenSubspace (pullback a f))
    (hZ : IsFinite (Z.ι ≫ pullback.fst a f)) :
    (over (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})).presheaf
      (Point.hom (Point.of a Z hZ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
