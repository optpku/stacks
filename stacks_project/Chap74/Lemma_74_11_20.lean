/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

variable (S : Scheme.{u})

/- Lemma 74.11.20: the property `P(f)` given by “`f` is quasi-affine” is fpqc
local on the base. -/
@[stacks 0423] #check
  (AlgebraicGeometry.AlgebraicSpace.QuasiAffine.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.QuasiAffine S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y) {R : Presieve Y}
  (hR : R ∈ (fpqcPrecoverage S).coverings Y)

#check
  (CategoryTheory.MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd hR :
    AlgebraicSpace.QuasiAffine f ↔
      ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
        R g → AlgebraicSpace.QuasiAffine (pullback.snd f g))
