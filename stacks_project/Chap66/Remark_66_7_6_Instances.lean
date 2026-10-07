module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.Gorenstein.Local
public import ReasLib.RingTheory.Normal.Ring
public import stacks_project.Chap66.Definition_66_25_2_RegularAt
public import stacks_project.Chap66.Remark_66_7_6_LocalRing

/-!
# Étale-invariance of listed local-ring properties

The local-ring properties listed in Remark 66.7.6 are invariant under étale maps at
corresponding primes, and therefore determine étale-local germ properties via
`GermProperty.ofLocalRing`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped ENat

universe u

noncomputable section

namespace AlgebraicGeometry

/-- Noetherianity of local rings is étale-local at corresponding primes. -/
theorem isNoetherianRing_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes fun R ↦ IsNoetherianRing R :=
  sorry

/-- The germ property of having a Noetherian stalk is étale-local. -/
theorem ofLocalRing_isNoetherianRing_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ IsNoetherianRing R).IsEtaleLocal :=
  sorry

/-- Having Krull dimension `d` is étale-local at corresponding primes. -/
theorem ringKrullDim_isEtaleLocalAtPrimes (d : WithBot ℕ∞) :
    IsEtaleLocalAtPrimes fun R ↦ ringKrullDim R = d :=
  sorry

/-- The germ property of having stalk of Krull dimension `d` is étale-local. -/
theorem ofLocalRing_ringKrullDim_isEtaleLocal (d : WithBot ℕ∞) :
    (GermProperty.ofLocalRing fun R ↦ ringKrullDim R = d).IsEtaleLocal :=
  sorry

/-- Regularity of local rings is étale-local at corresponding primes. -/
theorem isRegularLocalRing_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes fun R ↦ IsRegularLocalRing R :=
  sorry

/-- The germ property of having a regular local stalk is étale-local. -/
theorem ofLocalRing_isRegularLocalRing_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ IsRegularLocalRing R).IsEtaleLocal :=
  sorry

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

/-- The germ property of having a discrete valuation stalk is étale-local. -/
theorem ofLocalRing_isDiscreteValuationRing_isEtaleLocal :
    (GermProperty.ofLocalRing isDiscreteValuationLocalRing).IsEtaleLocal :=
  sorry

/-- Reducedness of local rings is étale-local at corresponding primes. -/
theorem isReduced_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes fun R ↦ _root_.IsReduced R :=
  sorry

/-- The germ property of having a reduced stalk is étale-local. -/
theorem ofLocalRing_isReduced_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ _root_.IsReduced R).IsEtaleLocal :=
  sorry

/-- Normality of local rings is étale-local at corresponding primes. -/
theorem isNormalRing_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes fun R ↦ IsNormalRing R :=
  sorry

/-- The germ property of having a normal stalk is étale-local. -/
theorem ofLocalRing_isNormalRing_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ IsNormalRing R).IsEtaleLocal :=
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

/-- The germ property of having a Noetherian stalk of depth `k` is étale-local. -/
theorem ofLocalRing_isNoetherianOfDepth_isEtaleLocal (k : ℕ) :
    (GermProperty.ofLocalRing (isNoetherianOfDepth k)).IsEtaleLocal :=
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

/-- The germ property of having a Noetherian Cohen–Macaulay stalk is étale-local. -/
theorem ofLocalRing_isNoetherianCohenMacaulay_isEtaleLocal :
    (GermProperty.ofLocalRing isNoetherianCohenMacaulay).IsEtaleLocal :=
  sorry

/-- Being a Gorenstein local ring is étale-local at corresponding primes. -/
theorem isGorensteinLocalRing_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes fun R ↦ IsGorensteinLocalRing R :=
  sorry

/-- The germ property of having a Gorenstein local stalk is étale-local. -/
theorem ofLocalRing_isGorensteinLocalRing_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ IsGorensteinLocalRing R).IsEtaleLocal :=
  sorry

namespace AlgebraicSpace

/-- Regularity of an algebraic space at a point is the statement that the local ring at that
point is a regular local ring. -/
theorem RegularAt_iff_localRingHas {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    RegularAt X x ↔ localRingHas (fun R ↦ IsRegularLocalRing R) X x :=
  sorry

end AlgebraicSpace

end AlgebraicGeometry
