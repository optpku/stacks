module

public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

/-!
# Nagata Rings and Japanese Domains

This file defines the N-1, N-2 (Japanese), universally Japanese, and Nagata ring conditions.

## Main definitions

* `IsN1Ring` — a domain whose integral closure in its fraction field is finite.
* `IsN2Ring` — a domain (Japanese) where integral closure in every finite extension is finite.
* `UniversallyJapaneseRing` — every finite type domain algebra is N-2.
* `NagataRing` — Noetherian ring whose quotients by primes are N-2.

## Main results

* Every N-2 ring is N-1.
* Every field is N-2.
-/

universe u v

section

variable (R : Type u) [CommRing R] [IsDomain R]

/-- An N-1 domain is a domain whose integral closure in its fraction field is a finite module
over the domain. -/
@[stacks 032F]
class IsN1Ring : Prop where
  /-- The integral closure of `R` in its fraction field is finite over `R`. -/
  integralClosure_finite : Module.Finite R (integralClosure R (FractionRing R))

/-- An N-2 ring (Japanese domain) is a domain such that for every finite extension of its
fraction field, the integral closure of the domain in that extension is finite. -/
@[stacks 032F]
class IsN2Ring : Prop where
  /-- The integral closure of `R` in every finite extension of its fraction field is finite. -/
  integralClosure_finite
    (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L] :
    Module.Finite R (integralClosure R L)

attribute [instance] IsN1Ring.integralClosure_finite
attribute [instance] IsN2Ring.integralClosure_finite

end

namespace IsN2Ring

variable {R : Type u} [CommRing R] [IsDomain R]
variable (L : Type v) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
variable [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]

/-- The N-2 finiteness for an arbitrary-universe finite extension. -/
theorem integralClosure_finite_of_finiteDimensional [hR : IsN2Ring R] :
    Module.Finite R (integralClosure R L) := by
  -- Local instance justification (proof-local temporary data): shrink the extension for N-2.
  letI : Small.{u} L := Module.Finite.small (FractionRing R) L
  -- Local instance justification (defeq pin): transport the scalar tower through shrinking.
  letI : IsScalarTower R (FractionRing R) (Shrink.{u} L) :=
    LinearEquiv.isScalarTower (FractionRing R) (Shrink.linearEquiv R L)
  exact Module.Finite.equiv (Shrink.algEquiv R L).mapIntegralClosure.toLinearEquiv

attribute [instance] integralClosure_finite_of_finiteDimensional

end IsN2Ring

/-- A field is N-2: it has finite normalization in every finite extension. -/
noncomputable instance (K : Type u) [Field K] : IsN2Ring K where
  integralClosure_finite := by
    intro L _ _ _ _ _
    have hfinL : Module.Finite K L := by
      let e₁ : FractionRing K ≃+* K := (FractionRing.algEquiv K K).toRingEquiv
      let e₂ : L ≃+* L := RingEquiv.refl _
      -- Local instance justification (proof-local temporary data): expose finite dimensionality.
      letI : Module.Finite (FractionRing K) L := inferInstance
      let f : L ≃ₐ[K] L := AlgEquiv.refl
      have he : RingHom.comp (algebraMap K L) ↑e₁ =
          RingHom.comp ↑e₂ (algebraMap (FractionRing K) L) := by
        ext x
        simpa [e₁, e₂] using IsFractionRing.algEquiv_commutes (FractionRing.algEquiv K K) f x
      exact Module.Finite.of_equiv_equiv e₁ e₂ he
    -- Local instance justification (proof-local temporary data): use transported finiteness.
    letI : Module.Finite K L := hfinL
    -- Local instance justification (search instability): infer integrality from module finiteness.
    letI : Algebra.IsIntegral K L := inferInstance
    have htop : integralClosure K L = ⊤ := integralClosure_eq_top_iff.2 inferInstance
    let e : integralClosure K L ≃ₐ[K] L :=
      (Subalgebra.equivOfEq (integralClosure K L) ⊤ htop).trans Subalgebra.topEquiv
    exact Module.Finite.equiv e.toLinearEquiv.symm

/-- Every N-2 ring is N-1. -/
instance (R : Type u) [CommRing R] [IsDomain R] [h : IsN2Ring R] : IsN1Ring R where
  integralClosure_finite := h.integralClosure_finite (FractionRing R)

section

variable (R : Type u) [CommRing R]

/-- A ring is universally Japanese if every finite type `R`-algebra that is a domain is N-2. -/
@[stacks 032R]
class UniversallyJapaneseRing : Prop where
  /-- Every finite type domain over a universally Japanese ring is N-2. -/
  finiteType_algebra_isN2Ring {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [IsDomain S] : IsN2Ring S

attribute [instance] UniversallyJapaneseRing.finiteType_algebra_isN2Ring

/-- A Nagata ring is a Noetherian ring whose quotient by every prime ideal is N-2. -/
@[stacks 032R]
class NagataRing : Prop extends IsNoetherianRing R where
  /-- The quotient of a Nagata ring by any prime ideal is N-2. -/
  quotient_isN2Ring (p : Ideal R) [p.IsPrime] : IsN2Ring (R ⧸ p)

attribute [instance] NagataRing.quotient_isN2Ring

end
