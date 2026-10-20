/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization

/-!
# Branch numbers of local rings

This leaf owns the numerical branch invariants attached to a chosen
henselization or strict henselization of a local ring.  The relevant
minimal-prime set is kept explicit, so the definitions are independent of a
particular construction of either local algebra.
-/

@[expose] public section

universe u v

noncomputable section

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The branch number of `A` is the number of minimal primes of a chosen
henselization `Ah`. -/
@[stacks 0C26 "branch number"]
abbrev branchNumber
    (Ah : Type v) [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah] : ℕ∞ :=
  (minimalPrimes Ah).encard

/-- The geometric branch number of `A` is the number of minimal primes of a
chosen strict henselization `Ash`. -/
@[stacks 0C26 "geometric branch number"]
abbrev geometricBranchNumber
    (Ash : Type v) [CommRing Ash] [Algebra A Ash]
    [IsStrictHenselizationOf A Ash] : ℕ∞ :=
  (minimalPrimes Ash).encard

/-- A local ring has geometric branch number `n` if some strict henselization
has exactly `n` minimal primes. -/
def hasGeometricBranchNumber (n : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] :
    Prop :=
  ∃ (Ash : Type u) (_ : CommRing Ash) (_ : Algebra R Ash)
    (_ : IsStrictHenselizationOf R Ash), geometricBranchNumber R Ash = n

/-- `hasGeometricBranchNumber n R` is the existence of a strict henselization of
`R` with geometric branch number `n`. -/
theorem hasGeometricBranchNumber_def (n : ℕ) (R : Type u) [CommRing R]
    [IsLocalRing R] :
    hasGeometricBranchNumber n R ↔
      ∃ (Ash : Type u) (_ : CommRing Ash) (_ : Algebra R Ash)
        (_ : IsStrictHenselizationOf R Ash), geometricBranchNumber R Ash = n :=
  sorry

namespace hasGeometricBranchNumber

/-- A strict henselization of `R` with geometric branch number `n` witnesses
`hasGeometricBranchNumber n R`. -/
theorem of {n : ℕ} {R : Type u} [CommRing R] [IsLocalRing R] (Ash : Type u)
    [CommRing Ash] [Algebra R Ash] [IsStrictHenselizationOf R Ash]
    (h : geometricBranchNumber R Ash = n) : hasGeometricBranchNumber n R :=
  sorry

/-- A local ring with geometric branch number `n` admits a strict henselization
with that geometric branch number. -/
theorem spec {n : ℕ} {R : Type u} [CommRing R] [IsLocalRing R]
    (h : hasGeometricBranchNumber n R) :
    ∃ (Ash : Type u) (_ : CommRing Ash) (_ : Algebra R Ash)
      (_ : IsStrictHenselizationOf R Ash), geometricBranchNumber R Ash = n :=
  sorry

/-- At most one natural number is the geometric branch number of a local ring. -/
theorem unique {R : Type u} [CommRing R] [IsLocalRing R] {n m : ℕ}
    (hn : hasGeometricBranchNumber n R) (hm : hasGeometricBranchNumber m R) :
    n = m :=
  sorry

end hasGeometricBranchNumber

/-- The geometric branch number of a local ring is independent of the chosen
strict henselization: it equals `n` for some strict henselization if and only
if it equals `n` for every strict henselization. -/
theorem hasGeometricBranchNumber_iff (n : ℕ) (R : Type u) [CommRing R]
    [IsLocalRing R] :
    hasGeometricBranchNumber n R ↔
      ∀ (Ash : Type u) [CommRing Ash] [Algebra R Ash]
        [IsStrictHenselizationOf R Ash], geometricBranchNumber R Ash = n :=
  sorry
