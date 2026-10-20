module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.RingTheory.Flat.Locus
public import ReasLib.RingTheory.Ideal.FlatQuotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed-fiber flat quotient ideals

This file owns the least ideal cutting out a quotient whose closed fiber is flat, together with
its local base-change criteria over Noetherian and finite-type bases.

@stack 0526
@stack 0527
@stack 0528
-/

@[expose] public section

open PrimeSpectrum IsLocalRing
open scoped TensorProduct

universe u v w x

namespace Ideal

variable {R : Type u} [CommRing R]

/-- An ideal gives a closed-fiber flat quotient when it lies in the maximal ideal and the
quotient module is flat at every prime above the closed point. -/
@[stacks 0526 "closed-fiber flat quotient ideal"]
abbrev IsClosedFiberFlatQuotient (J : Ideal R)
    (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module S M] [IsLocalRing R] : Prop :=
  let Sbar := S ⧸ Ideal.map (algebraMap R S) J
  let Mbar := M ⧸ ((Ideal.map (algebraMap R S) J) • (⊤ : Submodule S M))
  let _ : Module (R ⧸ J) Mbar := Module.compHom _ (algebraMap (R ⧸ J) Sbar)
  let _ : IsScalarTower (R ⧸ J) Sbar Mbar :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let mbar := Ideal.map (Ideal.Quotient.mk J) (maximalIdeal R)
  let Kbar := Ideal.map (algebraMap (R ⧸ J) Sbar) mbar
  J ≤ maximalIdeal R ∧
    zeroLocus (Kbar : Set Sbar) ⊆ Module.flatOverBaseLocus (R ⧸ J) Sbar Mbar

namespace IsClosedFiberFlatQuotient

variable {S : Type v} {M : Type w}
variable [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsNoetherianRing R] [IsNoetherianRing S]
variable [IsAdicComplete (maximalIdeal R) R]
variable [AddCommGroup M] [Module S M] [Module.Finite S M]

/-- Lemma 15.20.1: over a complete Noetherian local ring, the closed-fiber flat quotient ideals
have a least element. -/
@[stacks 0526 "Lemma 15.20.1"]
theorem exists_isLeast :
    ∃ I : Ideal R, IsLeast {J : Ideal R | J.IsClosedFiberFlatQuotient S M} I := sorry

-- Local instance justification (instance diamond): the tensor product uses the target ring as
-- its right scalar ring, as in the source base-change triple.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R' : Type x} [CommRing R'] [Algebra R R']
variable [IsLocalRing R'] [IsLocalHom (algebraMap R R')]

local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

/-- Lemma 15.20.2: for a Noetherian local target, closed-fiber flatness after base change is
equivalent to the least ideal mapping to zero. -/
@[stacks 0527 "Lemma 15.20.2"]
theorem baseChange_iff_map_eq_bot_of_noetherian [IsNoetherianRing R']
    {I : Ideal R} (hI : IsLeast {J : Ideal R | J.IsClosedFiberFlatQuotient S M} I) :
    zeroLocus (Ideal.map (algebraMap R' S') (maximalIdeal R') : Set S') ⊆
        Module.flatOverBaseLocus R' S' M' ↔
      Ideal.map (algebraMap R R') I = ⊥ := sorry

/-- Lemma 15.20.3: when `R → S` is finite type, the same base-change criterion holds for
every local target ring. -/
@[stacks 0528 "Lemma 15.20.3"]
theorem baseChange_iff_map_eq_bot_of_finiteType [Algebra.FiniteType R S]
    {I : Ideal R} (hI : IsLeast {J : Ideal R | J.IsClosedFiberFlatQuotient S M} I) :
    zeroLocus (Ideal.map (algebraMap R' S') (maximalIdeal R') : Set S') ⊆
        Module.flatOverBaseLocus R' S' M' ↔
      Ideal.map (algebraMap R R') I = ⊥ := sorry

end IsClosedFiberFlatQuotient

end Ideal
