/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Injective.ResidueField
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.64.7 (Injectives): for an Artinian local ring `A` that is injective
as an `A`-module, the residue-field dual has dimension one over the residue field. -/
@[stacks 0GRZ] #check
  (IsLocalRing.finrank_linearMap_residueField_self_eq_one :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      [Module.Injective A A],
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A →ₗ[A] A) = 1)
