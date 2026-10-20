/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.IsoClasses

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/- Lemma 99.11.7 (1): universal preservation of the structure sheaf makes the
section-rigidified Picard projection fibred in setoids. -/
@[stacks 0D2B] #check
  (AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.instIsFiberedInSetoids :
    ∀ (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
      [Hom.IsIsoBaseChangeStructurePushforward f],
      Functor.IsFibered.InSetoids (Picard.WithSection.p f σ hσ))

/- Lemma 99.11.7 (2): fibre isomorphism classes are the coproduct over maps
from the test scheme of the kernels of section pullback on Picard groups. -/
@[stacks 0D2B] #check
  (AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.isoClassEquiv :
    ∀ (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
      [Hom.IsIsoBaseChangeStructurePushforward f] (T : Over S),
      isomorphismClasses.obj (Cat.of ((Picard.WithSection.p f σ hσ).Fiber T)) ≃
        Σ h : ofOver T ⟶ B,
          (Picard.WithSection.sectionPicard f σ hσ (CostructuredArrow.mk h)).ker)
