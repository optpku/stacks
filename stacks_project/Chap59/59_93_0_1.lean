/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap59.«59_93_0_1_Comparison»
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- 59.93.0.1 -/
@[stacks 0GJN]
#check (AlgebraicGeometry.Scheme.EtaleVanishingCycles.alpha :
  ∀ {X S : Scheme.{u}}
    (f : X ⟶ S) (xbar : GeometricPoint X)
    (tbar : GeometricPoint (strictHenselizationAt S (xbar.map f)))
    (K : AlgebraicGeometry.Scheme.EtaleVanishingCycles.Complexes X),
    (AlgebraicGeometry.Scheme.EtaleVanishingCycles.derivedSections
      (strictHenselizationAt X xbar)).obj
        ((AlgebraicGeometry.Scheme.EtaleVanishingCycles.derivedInverseImage
          (AlgebraicGeometry.Scheme.StrictHenselization.toScheme X xbar)).obj K) ⟶
      (AlgebraicGeometry.Scheme.EtaleVanishingCycles.derivedSections
        (pullback tbar.hom
          (AlgebraicGeometry.Scheme.StrictHenselization.map f xbar))).obj
        ((AlgebraicGeometry.Scheme.EtaleVanishingCycles.derivedInverseImage
          (pullback.snd tbar.hom
            (AlgebraicGeometry.Scheme.StrictHenselization.map f xbar))).obj
          ((AlgebraicGeometry.Scheme.EtaleVanishingCycles.derivedInverseImage
            (AlgebraicGeometry.Scheme.StrictHenselization.toScheme X xbar)).obj K)))

end AlgebraicGeometry.Scheme
