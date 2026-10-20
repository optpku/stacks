/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

@[expose] public section

universe u v

namespace RingHom.DimensionFormula

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsDomain A] [IsDomain B]
variable [IsLocalRing A] [IsLocalRing B]

/-- For an injective flat essentially finite-type local homomorphism of domains,
the dimension of the closed fiber plus the residue-field transcendence degree
equals the transcendence degree of the map. -/
theorem closedFiber_add_residueTrdeg_eq_trdeg
    (f : A →+* B) [IsLocalHom f] (h_injective : Function.Injective f)
    (h_essentiallyFiniteType : f.EssFiniteType) (h_flat : f.Flat) :
    -- Local instance justification (defeq pin): `f.toAlgebra` identifies `algebraMap A B` for the residue-field and transcendence-degree terms.
    letI : Algebra A B := f.toAlgebra
    ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map f) +
        (Cardinal.toNat
          (Algebra.trdeg (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) :
          WithBot ℕ∞) =
      (Cardinal.toNat (Algebra.trdeg A B) : WithBot ℕ∞) := sorry

end RingHom.DimensionFormula
