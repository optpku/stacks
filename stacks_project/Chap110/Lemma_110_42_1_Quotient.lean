/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.Quotient.FormallyEtale
public import ReasLib.RingTheory.LocalRing.ResidueField.NonFlat

@[expose] public section

universe u

#check (Ideal.Quotient.formallyEtale_mk_iff :
  ∀ {R : Type u} [CommRing R] (J : Ideal R),
    (Ideal.Quotient.mk J).FormallyEtale ↔ IsIdempotentElem J)

#check (Ideal.Quotient.not_flat_mk_of_isLocalRing :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] {J : Ideal R},
    J ≠ ⊥ → J ≠ ⊤ → ¬ (Ideal.Quotient.mk J).Flat)

#check (IsLocalRing.residue_not_flat :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R],
    ¬ IsField R → ¬ (IsLocalRing.residue R).Flat)
