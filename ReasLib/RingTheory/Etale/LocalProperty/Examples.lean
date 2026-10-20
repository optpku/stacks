module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.Gorenstein.Local
public import ReasLib.RingTheory.Normal.Ring
public import ReasLib.RingTheory.Etale.LocalProperty
public import ReasLib.RingTheory.Etale.Noetherian
public import ReasLib.RingTheory.KrullDimension.Etale
public import ReasLib.RingTheory.Etale.RegularLocal

/-!
# Local-ring properties invariant at étale primes

Discrete valuation, reducedness, normality, Noetherian depth, Noetherian Cohen–Macaulayness,
and Gorensteinness are invariant at corresponding primes of étale algebras.
-/

@[expose] public section

universe u

namespace LocalRingProperty

/-- A local ring which is a discrete valuation ring. -/
def isDiscreteValuationLocalRing (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  IsDomain R ∧ ∀ [IsDomain R], IsDiscreteValuationRing R

/-- A local ring is a discrete valuation ring precisely when it is a domain satisfying
`IsDiscreteValuationRing`. -/
theorem isDiscreteValuationLocalRing_iff (R : Type u) [CommRing R] [IsLocalRing R] :
    isDiscreteValuationLocalRing R ↔
      IsDomain R ∧ ∀ [IsDomain R], IsDiscreteValuationRing R :=
  Iff.rfl

/-- Being a discrete valuation ring is étale-local at corresponding primes. -/
theorem isDiscreteValuationRing_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes isDiscreteValuationLocalRing :=
  sorry

/-- Reducedness of local rings is étale-local at corresponding primes. -/
theorem isReduced_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes fun R ↦ _root_.IsReduced R :=
  sorry

/-- Normality of local rings is étale-local at corresponding primes. -/
theorem isNormalRing_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes fun R ↦ IsNormalRing R :=
  sorry

/-- A local ring that is Noetherian of depth `k`. -/
def isNoetherianOfDepth (k : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧ moduleDepth R R = k

/-- A local ring is Noetherian of depth `k` if and only if it is Noetherian and
`moduleDepth R R = k`. -/
theorem isNoetherianOfDepth_iff (k : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] :
    isNoetherianOfDepth k R ↔ IsNoetherianRing R ∧ moduleDepth R R = k :=
  Iff.rfl

/-- Being Noetherian of depth `k` is étale-local at corresponding primes. -/
theorem isNoetherianOfDepth_isEtaleLocalAtPrimes (k : ℕ) :
    IsEtaleLocalAtPrimes (isNoetherianOfDepth k) :=
  sorry

/-- A local ring that is Noetherian and Cohen–Macaulay as a module over itself. -/
def isNoetherianCohenMacaulay (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧ ∀ [IsNoetherianRing R], Module.CohenMacaulay R R

/-- A local ring is Noetherian and Cohen–Macaulay if and only if it is Noetherian and
Cohen–Macaulay as a module over itself. -/
theorem isNoetherianCohenMacaulay_iff (R : Type u) [CommRing R] [IsLocalRing R] :
    isNoetherianCohenMacaulay R ↔
      IsNoetherianRing R ∧ ∀ [IsNoetherianRing R], Module.CohenMacaulay R R :=
  Iff.rfl

/-- Being Noetherian and Cohen–Macaulay is étale-local at corresponding primes. -/
theorem isNoetherianCohenMacaulay_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes isNoetherianCohenMacaulay :=
  sorry

/-- Being a Gorenstein local ring is étale-local at corresponding primes. -/
theorem isGorensteinLocalRing_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes fun R ↦ IsGorensteinLocalRing R :=
  sorry

end LocalRingProperty
