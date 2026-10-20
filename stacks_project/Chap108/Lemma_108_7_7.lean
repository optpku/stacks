/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import stacks_project.Chap71.Definition_71_18_1_StrictTransform
public import stacks_project.Chap108.Lemma_108_5_10_Hilbert
public import stacks_project.Chap108.Lemma_108_6_1_ProperOver

/-!
# Lemma 108.7.7

The Hilbert-polynomial algebraic space of closed subschemes, taken with
respect to a relatively ample invertible module, is proper over the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonoidalCategory.InvertiblePower

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

/-- Lemma 108.7.7: if `f : X ⟶ B` is a proper morphism of finite presentation of
algebraic spaces and `L` is an invertible `𝒪_X`-module ample on `X/B` in the
sense of Definition 71.14.1, then the algebraic space `Hilb^P_{X/B}` parametrizing
closed subschemes with Hilbert polynomial `P` with respect to `L` is proper over
`B`. Here `Hilb^P_{X/B}` is the Hilbert-polynomial locus `quotHilbert` of `𝒪_X`. -/
@[stacks 0DPH]
theorem hilbertPolynomial_isProperOver {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [Proper f] [FinitePresentation f] (L : X.Modules)
    [isInvertibleObject L] (h_representable : yoneda.relativelyRepresentable f)
    (h_ample : ∀ {Z W : Over S} {g : ofOver Z ⟶ B} {pX : ofOver W ⟶ X}
      {pZ : W ⟶ Z}, IsPullback pX (ofOverMap pZ) f g →
        AlgebraicGeometry.RelativelyAmple pZ.left
          ((restrictFunctor (𝟙 (ofOver W)) ⋙ Quot.ofOverToScheme W).obj
            ((Modules.pullback pX).obj L)))
    (P : ℤ → ℤ) :
    IsProperOver
      (Quot.quotHilbert f (SheafOfModules.unit (structureSheaf X)) L P).toFunctor :=
  sorry

/-- Properness of the Hilbert-polynomial functor means some representing morphism
of algebraic spaces over `B` is proper. -/
theorem hilbertPolynomial_isProperOver_spec {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B) [Proper f] [FinitePresentation f]
    (L : X.Modules) [isInvertibleObject L]
    (h_representable : yoneda.relativelyRepresentable f)
    (h_ample : ∀ {Z W : Over S} {g : ofOver Z ⟶ B} {pX : ofOver W ⟶ X}
      {pZ : W ⟶ Z}, IsPullback pX (ofOverMap pZ) f g →
        AlgebraicGeometry.RelativelyAmple pZ.left
          ((restrictFunctor (𝟙 (ofOver W)) ⋙ Quot.ofOverToScheme W).obj
            ((Modules.pullback pX).obj L)))
    (P : ℤ → ℤ) :
    IsProperOver
        (Quot.quotHilbert f (SheafOfModules.unit (structureSheaf X)) L P).toFunctor ↔
      ∃ (Q : AlgebraicSpace S) (π : Q ⟶ B),
        Proper π ∧
          Nonempty
            ((Quot.quotHilbert f (SheafOfModules.unit (structureSheaf X)) L P).toFunctor ≅
              yonedaOver π) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
