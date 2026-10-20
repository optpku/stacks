/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import stacks_project.Chap108.Lemma_108_6_1_ProperOver
public import stacks_project.Chap108.Lemma_108_5_10_Hilbert

/-!
# Lemma 108.6.3

The Hilbert Quot algebraic space of finitely presented quotients of a
finitely presented module, with Hilbert polynomial taken with respect to a
relatively ample invertible module, is proper over the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonoidalCategory.InvertiblePower

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- Lemma 108.6.3: if `f : X ⟶ B` is a proper morphism of finite presentation of
algebraic spaces, `F` is a finitely presented `𝒪_X`-module, and `L` is an
invertible `𝒪_X`-module ample on `X/B` in the sense of Definition 71.14.1, then
the algebraic space `Quot^P_{F/X/B}` parametrizing quotients of `F` with Hilbert
polynomial `P` with respect to `L` is proper over `B`. -/
@[stacks 0DPC]
theorem quotHilbert_isProperOver {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [Proper f] [FinitePresentation f] (F L : X.Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] [isInvertibleObject L]
    (h_representable : yoneda.relativelyRepresentable f)
    (h_ample : ∀ {Z W : Over S} {g : ofOver Z ⟶ B} {pX : ofOver W ⟶ X}
      {pZ : W ⟶ Z}, IsPullback pX (ofOverMap pZ) f g →
        AlgebraicGeometry.RelativelyAmple pZ.left
          ((restrictFunctor (𝟙 (ofOver W)) ⋙ ofOverToScheme W).obj
            ((Modules.pullback pX).obj L)))
    (P : ℤ → ℤ) :
    IsProperOver (quotHilbert f F L P).toFunctor :=
  sorry

/-- Properness of `quotHilbert` means some representing morphism of algebraic
spaces over `B` is proper. -/
theorem quotHilbert_isProperOver_spec {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [Proper f] [FinitePresentation f] (F L : X.Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] [isInvertibleObject L]
    (h_representable : yoneda.relativelyRepresentable f)
    (h_ample : ∀ {Z W : Over S} {g : ofOver Z ⟶ B} {pX : ofOver W ⟶ X}
      {pZ : W ⟶ Z}, IsPullback pX (ofOverMap pZ) f g →
        AlgebraicGeometry.RelativelyAmple pZ.left
          ((restrictFunctor (𝟙 (ofOver W)) ⋙ ofOverToScheme W).obj
            ((Modules.pullback pX).obj L)))
    (P : ℤ → ℤ) :
    IsProperOver (quotHilbert f F L P).toFunctor ↔
      ∃ (Q : AlgebraicSpace S) (π : Q ⟶ B),
        Proper π ∧
          Nonempty ((quotHilbert f F L P).toFunctor ≅ yonedaOver π) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
