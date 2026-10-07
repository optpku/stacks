module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AtPrime
public import ReasLib.RingTheory.FormalFiber.FieldProperty.Basic

@[expose] public section

/-!
# Formal fibers with a field-algebra property

@stack 0BIR
@stack 0BIS

This file owns the ring-level predicates built from a
`FieldAlgebraProperty`: the formal fibers of a local ring, the `P`-ring
condition, and its prime-pair presentation.
-/

open IsLocalRing

universe u

namespace FieldAlgebraProperty

/-- A local ring has formal fibers with property `P` when every residue-field
fiber of its maximal-ideal completion has `P`. -/
@[stacks 0BIR "formal fibers with a field-algebra property"]
abbrev HoldsOnFormalFibers
    (P : FieldAlgebraProperty.{u, u}) (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ q : PrimeSpectrum A,
    P q.asIdeal.ResidueField
      (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))

end FieldAlgebraProperty

/-- A `P`-ring is a Noetherian ring whose completed local rings have formal
fibers with the field-algebra property `P`. -/
@[stacks 0BIR "P-rings"]
class IsPRing (P : FieldAlgebraProperty.{u, u}) (R : Type u)
    [CommRing R] : Prop extends IsNoetherianRing R where
  /-- Every fiber of `R_p → (R_p)^∧` has property `P`. -/
  satisfiesPFormalFiberCondition (p : PrimeSpectrum R)
      (q : PrimeSpectrum (Localization.AtPrime p.asIdeal)) :
      P q.asIdeal.ResidueField
        (q.asIdeal.Fiber (PrimeSpectrum.CompletedLocalRing p))

namespace FieldAlgebraProperty

/-- The prime-pair form of the formal-fiber condition for a `P`-ring. -/
@[stacks 0BIS "prime-pair formal-fiber condition"]
abbrev HoldsOnPrimePairFibers
    (P : FieldAlgebraProperty.{u, u}) (R : Type u) [CommRing R] : Prop :=
  ∀ p q : PrimeSpectrum R, q.asIdeal ≤ p.asIdeal →
    P q.asIdeal.ResidueField
      (q.asIdeal.Fiber (PrimeSpectrum.CompletedLocalRing p))

/-- Formal fibers of the local ring `R_p` are indexed by the primes `q ≤ p` of `R`. -/
@[stacks 0BIS "formal fibers of a prime localization"]
theorem holdsOnFormalFibers_localizationAtPrime_iff
    (P : FieldAlgebraProperty.{u, u}) (R : Type u) [CommRing R]
    (p : PrimeSpectrum R) :
    P.HoldsOnFormalFibers (Localization.AtPrime p.asIdeal) ↔
      ∀ q : PrimeSpectrum R, q.asIdeal ≤ p.asIdeal →
        P q.asIdeal.ResidueField
          (q.asIdeal.Fiber (PrimeSpectrum.CompletedLocalRing p)) := sorry

end FieldAlgebraProperty

namespace IsPRing

variable {P : FieldAlgebraProperty.{u, u}} {R : Type u} [CommRing R]

/-- A `P`-ring has the required formal fibers at each prime localization. -/
@[stacks 0BIR "P-ring formal fibers at a prime"]
theorem holdsOnFormalFibers (hR : IsPRing P R) (p : PrimeSpectrum R) :
    P.HoldsOnFormalFibers (Localization.AtPrime p.asIdeal) := sorry

/-- A Noetherian ring is a `P`-ring when every prime localization has the required formal
fibers. -/
theorem of_forall_holdsOnFormalFibers [IsNoetherianRing R]
    (hR : ∀ p : PrimeSpectrum R,
      P.HoldsOnFormalFibers (Localization.AtPrime p.asIdeal)) :
    IsPRing P R := sorry

/-- The defining formal-fiber criterion for a Noetherian `P`-ring. -/
@[stacks 0BIR "P-ring formal-fiber criterion"]
theorem iff_forall_holdsOnFormalFibers [IsNoetherianRing R] :
    IsPRing P R ↔
      ∀ p : PrimeSpectrum R,
        P.HoldsOnFormalFibers (Localization.AtPrime p.asIdeal) := sorry

/-- A `P`-ring satisfies the equivalent prime-pair formal-fiber condition. -/
@[stacks 0BIS "P-ring prime-pair formal fibers"]
theorem holdsOnPrimePairFibers (hR : IsPRing P R) :
    P.HoldsOnPrimePairFibers R := sorry

/-- A Noetherian ring satisfying the prime-pair formal-fiber condition is a `P`-ring. -/
theorem of_holdsOnPrimePairFibers [IsNoetherianRing R]
    (hR : P.HoldsOnPrimePairFibers R) :
    IsPRing P R := sorry

/-- The prime-pair presentation of the `P`-ring condition. -/
@[stacks 0BIS "prime-pair criterion for P-rings"]
theorem iff_holdsOnPrimePairFibers [IsNoetherianRing R] :
    IsPRing P R ↔ P.HoldsOnPrimePairFibers R := sorry

/-- Prime localization preserves the `P`-ring condition. -/
@[stacks 0BIR "P-rings localize at primes"]
theorem localizationAtPrime (hR : IsPRing P R) (p : PrimeSpectrum R) :
    IsPRing P (Localization.AtPrime p.asIdeal) := sorry

/-- A Noetherian ring is a `P`-ring when all its prime localizations are `P`-rings. -/
theorem of_localizationsAtPrime [IsNoetherianRing R]
    (hR : ∀ p : PrimeSpectrum R, IsPRing P (Localization.AtPrime p.asIdeal)) :
    IsPRing P R := sorry

end IsPRing
