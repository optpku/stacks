/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Standard
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Definition 29.30.1

This chapter entry is a compatibility facade for standard syntomic affine
morphisms.
-/

/- Definition 29.30.1: standard syntomic affine morphisms. -/
@[stacks 01UC] #check
  (AlgebraicGeometry.StandardSyntomic :
    {X S : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ S) →
      [AlgebraicGeometry.IsAffine X] → [AlgebraicGeometry.IsAffine S] → Prop)

#check
  (AlgebraicGeometry.standardSyntomic_appTop_syntomic :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine S],
      AlgebraicGeometry.StandardSyntomic f →
        RingHom.Syntomic
          (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.appTop f)))

#check
  (AlgebraicGeometry.standardSyntomic_syntomic :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine S],
      AlgebraicGeometry.StandardSyntomic f → AlgebraicGeometry.Syntomic f)
