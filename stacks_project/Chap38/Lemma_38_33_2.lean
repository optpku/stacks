/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Separation
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 38.33.2 (1): two finitely presented closed subschemes that do not meet over a
quasi-compact open have disjoint strict transforms after an admissible blowup. -/
@[stacks 0F3V] #check
  (AlgebraicGeometry.exists_isAdmissibleBlowup_disjointStrictTransforms :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) [AlgebraicGeometry.QuasiCompact U.ι]
    (Z₁ Z₂ : X.IdealSheafData)
    [AlgebraicGeometry.Scheme.Hom.FinitePresentation Z₁.subschemeι]
    [AlgebraicGeometry.Scheme.Hom.FinitePresentation Z₂.subschemeι],
    Disjoint ((Z₁.support : Set X) ∩ (Z₂.support : Set X)) (U : Set X) →
      ∃ (X' : AlgebraicGeometry.Scheme.{u}) (b : X' ⟶ X) (I : X.IdealSheafData),
      AlgebraicGeometry.IsAdmissibleBlowupCenter U b I ∧
        Disjoint
          (Set.range
            (AlgebraicGeometry.strictTransformSnd b (I.comap b) Z₁.subschemeι).base)
          (Set.range
            (AlgebraicGeometry.strictTransformSnd b (I.comap b) Z₂.subschemeι).base))

/- Lemma 38.33.2 (2): two disjoint constructible closed subsets of a quasi-compact open have
disjoint closures after an admissible blowup. -/
@[stacks 0F3V] #check
  (AlgebraicGeometry.exists_isAdmissibleBlowup_disjointConstructibleClosures :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) [AlgebraicGeometry.QuasiCompact U.ι]
    (T₁ T₂ : TopologicalSpace.Closeds U)
    (hT₁ : Topology.IsConstructible (T₁ : Set U))
    (hT₂ : Topology.IsConstructible (T₂ : Set U)),
    Disjoint T₁ T₂ →
      ∃ (X' : AlgebraicGeometry.Scheme.{u}) (b : X' ⟶ X),
      AlgebraicGeometry.IsAdmissibleBlowup U b ∧
        Disjoint
          (closure (b.base ⁻¹' Set.image U.ι.base (T₁ : Set U)))
          (closure (b.base ⁻¹' Set.image U.ι.base (T₂ : Set U))))
