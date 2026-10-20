/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Unramified.LocalRing
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 41.3.1: for an essentially finite type local homomorphism of Noetherian
local rings, formal unramifiedness is equivalent to equality of the extended maximal ideal
with the target maximal ideal and a finite separable extension of residue fields. -/
@[stacks 024M] #check
  (Algebra.FormallyUnramified.iff_localRingConditions :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
      [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B],
      Algebra.FormallyUnramified A B ↔
        (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B ∧
          (FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) ∧
            Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)))

end
