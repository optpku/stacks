/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DividedPowerThickening
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 60.7.3 -/
@[stacks 07I4] #check
  (AlgebraicGeometry.IsDividedPowerSchemeThickening :
    (T : AlgebraicGeometry.Scheme.{u}) →
      (J : T.IdealSheafData) →
      (h_quasiCoherent : J.toModule.IsQuasicoherent) →
      (γ : ∀ V : T.affineOpens, DividedPowers (J.ideal V)) →
      (h_compatible :
        ∀ (V : T.affineOpens) (f : Γ(T, V)),
          (γ V).IsDPMorphism (γ (T.affineBasicOpen f))
            (T.presheaf.map (CategoryTheory.homOfLE (T.basicOpen_le f)).op).hom) →
      Prop)
