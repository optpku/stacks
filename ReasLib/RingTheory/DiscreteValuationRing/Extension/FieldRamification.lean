module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.IntegralClosure
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Field-extension ramification over a DVR

This leaf owns the field-model version of the unramified predicate used by the Kummer
ramification alternatives.  The fraction field is an explicit parameter, so the API works for
any field model equipped with `IsFractionRing`, rather than forcing `FractionRing A` into every
downstream statement.

@stack 09E9
-/

universe u v w

open Ideal IsLocalRing

namespace DVR.Field

/-- A natural number is prime to every prime characteristic carried by a field. -/
@[stacks 09E9 "prime to the characteristic of a field"]
def PrimeToChar (κ : Type u) [Field κ] (n : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [CharP κ p], Nat.Coprime n p

namespace PrimeToChar

/-- The unit integer is prime to every field characteristic. -/
@[stacks 09E9 "one is prime to every field characteristic"]
theorem one (κ : Type u) [Field κ] : PrimeToChar κ 1 := sorry
-- Proof strategy: unfold `PrimeToChar`, introduce the characteristic prime, and use
-- `Nat.coprime_one_left`.

/-- Products of integers prime to a field characteristic remain prime to it. -/
@[stacks 09E9 "products prime to every field characteristic"]
theorem mul {κ : Type u} [Field κ] {m n : ℕ}
    (hm : PrimeToChar κ m) (hn : PrimeToChar κ n) :
    PrimeToChar κ (m * n) := sorry
-- Proof strategy: unfold `PrimeToChar`, specialize `hm` and `hn` at the same characteristic
-- prime, and combine them with the multiplicative closure lemmas for `Nat.Coprime`.

end PrimeToChar

/-- A natural number is prime to the residue characteristic of a local ring when it is coprime to
every prime characteristic carried by its residue field. -/
@[stacks 09E9 "prime to the residue characteristic"]
def PrimeToResidueChar (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) : Prop :=
  PrimeToChar (ResidueField A) n

namespace PrimeToResidueChar

/-- The unit integer is prime to every residue characteristic. -/
@[stacks 09E9 "one is prime to the residue characteristic"]
theorem one (A : Type u) [CommRing A] [IsLocalRing A] :
    PrimeToResidueChar A 1 := sorry
-- Proof strategy: unfold `PrimeToResidueChar` and apply `PrimeToChar.one` to `ResidueField A`.

/-- The product of two integers prime to the residue characteristic is again prime to it. -/
@[stacks 09E9 "products prime to the residue characteristic"]
theorem mul {A : Type u} [CommRing A] [IsLocalRing A] {m n : ℕ}
    (hm : PrimeToResidueChar A m) (hn : PrimeToResidueChar A n) :
    PrimeToResidueChar A (m * n) := sorry
-- Proof strategy: unfold `PrimeToResidueChar` and apply `PrimeToChar.mul hm hn`.

end PrimeToResidueChar

/-- A field extension is unramified over a DVR when every maximal normalization branch has
separable residue field and ramification index one. -/
@[stacks 09E9 "unramified field extension over a DVR"]
class IsUnramified
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] : Prop where
  /-- Residue fields on maximal branches are separable. -/
  residueField_separable (P : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] :
      @Algebra.IsSeparable (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField P)
        _ _ (Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) P)
  /-- Every maximal branch has ramification index one. -/
  ramificationIdx_eq_one (P : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] :
      P.ramificationIdx A = 1

/-- A field extension is tamely ramified over a DVR when each maximal normalization branch has
separable residue field and ramification index prime to the residue characteristic. -/
@[stacks 09E9 "tamely ramified field extension over a DVR"]
class IsTamelyRamified
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] : Prop where
  /-- Residue fields on maximal branches are separable. -/
  residueField_separable (P : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] :
      @Algebra.IsSeparable (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField P)
        _ _ (Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) P)
  /-- Every branch ramification index is prime to the residue characteristic. -/
  ramificationIdx_coprime (q : ℕ) [Fact q.Prime]
      [CharP (Ideal.ResidueField (maximalIdeal A)) q]
      (P : Ideal (integralClosure A L)) [P.IsMaximal]
      [P.LiesOver (maximalIdeal A)] :
      Nat.Coprime (P.ramificationIdx A) q

namespace IsUnramified

variable {A : Type u} {K : Type v} {L : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

/-- The residue-field clause of unramifiedness. -/
@[stacks 09E9 "unramified residue-field clause"]
theorem residueField_separable_of (h : IsUnramified A K L)
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] :
    @Algebra.IsSeparable (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField P)
      _ _ (Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) P) := sorry
-- Proof strategy: project `IsUnramified.residueField_separable` from `h` at the selected branch.

/-- The ramification-index clause of unramifiedness. -/
@[stacks 09E9 "unramified ramification-index clause"]
theorem ramificationIdx_eq_one_of (h : IsUnramified A K L)
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] :
    P.ramificationIdx A = 1 := sorry
-- Proof strategy: project `IsUnramified.ramificationIdx_eq_one` from `h` at `P`.

/-- The two branch conditions bundled by `DVR.Field.IsUnramified`. -/
@[stacks 09E9 "unramified branch specification"]
theorem spec (h : IsUnramified A K L) :
    (∀ (P : Ideal (integralClosure A L)) [P.IsMaximal]
        [P.LiesOver (maximalIdeal A)],
      @Algebra.IsSeparable (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField P)
        _ _ (Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) P)) ∧
      (∀ (P : Ideal (integralClosure A L)) [P.IsMaximal]
        [P.LiesOver (maximalIdeal A)], P.ramificationIdx A = 1) := sorry
-- Proof strategy: pair `h.residueField_separable_of` and `h.ramificationIdx_eq_one_of`, keeping
-- the branch and its class instances explicit in each component.

/-- Unramifiedness is equivalent to the residue-separability and index-one conditions on every
maximal branch. -/
@[stacks 09E9 "unramified branch characterization"]
theorem iff_forall :
    IsUnramified A K L ↔
      (∀ (P : Ideal (integralClosure A L)) [P.IsMaximal]
          [P.LiesOver (maximalIdeal A)],
        @Algebra.IsSeparable (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField P)
          _ _ (Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) P)) ∧
        (∀ (P : Ideal (integralClosure A L)) [P.IsMaximal]
          [P.LiesOver (maximalIdeal A)], P.ramificationIdx A = 1) := sorry
-- Proof strategy: use `IsUnramified.spec` forward; backward, construct `IsUnramified` by assigning
-- the two universally quantified hypotheses to its two class fields.

end IsUnramified

section CanonicalBridge

variable {A : Type u} {K : Type v} {L : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The field-model unramified predicate supplies Mathlib's canonical local unramified owner at
each maximal normalization branch.  The finite/separable hypotheses are the bridge assumptions
that make the integral-closure branch comparison an `Algebra.IsUnramifiedAt` statement. -/
@[stacks 09E9 "unramified field model to canonical local owner"]
theorem IsUnramified.isUnramifiedAt (h : IsUnramified A K L)
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] :
    Algebra.IsUnramifiedAt A P := sorry
-- Proof strategy: apply `Algebra.isUnramifiedAt_iff_map_eq`; obtain residue separability from
-- `h.residueField_separable_of P`, and turn `h.ramificationIdx_eq_one_of P` into the localized
-- maximal-ideal equality using the ramification-index-one criterion for a Dedekind branch.

/-- Under finite separable field-extension hypotheses, unramifiedness is equivalent to the
canonical `Algebra.IsUnramifiedAt` owner at every maximal branch. -/
@[stacks 09E9 "unramified field model canonical characterization"]
theorem IsUnramified.iff_forall_isUnramifiedAt :
    IsUnramified A K L ↔
      ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal]
        [P.LiesOver (maximalIdeal A)], Algebra.IsUnramifiedAt A P := sorry
-- Proof strategy: use `IsUnramified.isUnramifiedAt` forward; backward, apply
-- `Algebra.isUnramifiedAt_iff_map_eq` at every branch and reconstruct the separability and
-- ramification-index-one fields through the residue-map and ideal-power comparison theorems.

end CanonicalBridge

namespace IsTamelyRamified

variable {A : Type u} {K : Type v} {L : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

/-- The residue-field clause of tame ramification. -/
@[stacks 09E9 "tame residue-field clause"]
theorem residueField_separable_of (h : IsTamelyRamified A K L)
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] :
    @Algebra.IsSeparable (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField P)
      _ _ (Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) P) := sorry
-- Proof strategy: project `IsTamelyRamified.residueField_separable` from `h` at `P`.

/-- The prime-to-residue-characteristic clause of tame ramification. -/
@[stacks 09E9 "tame ramification-index clause"]
theorem ramificationIdx_coprime_of (h : IsTamelyRamified A K L)
    (q : ℕ) [Fact q.Prime] [CharP (Ideal.ResidueField (maximalIdeal A)) q]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] :
    Nat.Coprime (P.ramificationIdx A) q := sorry
-- Proof strategy: project `IsTamelyRamified.ramificationIdx_coprime` from `h`, specializing its
-- characteristic-prime parameters and branch to `q` and `P`.

/- The bundled predicate is the reusable form of the branchwise prime-to-characteristic clause. -/
/-- The ramification index of a maximal branch is prime to every characteristic of the base
residue field. -/
@[stacks 09E9 "tame branch index prime-to-characteristic predicate"]
theorem index_primeToChar (h : IsTamelyRamified A K L)
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] :
    PrimeToChar (Ideal.ResidueField (maximalIdeal A)) (P.ramificationIdx A) := sorry
-- Proof strategy: unfold `PrimeToChar`, introduce an arbitrary characteristic prime, and apply
-- `h.ramificationIdx_coprime_of` at that prime and `P`.

/-- The ramification index of a maximal branch is prime to the residue characteristic of the
base DVR, expressed through the reusable local-ring predicate. -/
@[stacks 09E9 "tame branch index prime to the residue characteristic"]
theorem index_primeToResidueChar (h : IsTamelyRamified A K L)
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] :
    PrimeToResidueChar A (P.ramificationIdx A) := sorry
-- Proof strategy: unfold `PrimeToResidueChar`; the result is exactly `h.index_primeToChar P` after
-- identifying the local residue field with `Ideal.ResidueField (maximalIdeal A)`.

/-- The two branch conditions bundled by `DVR.Field.IsTamelyRamified`. -/
@[stacks 09E9 "tame branch specification"]
theorem spec (h : IsTamelyRamified A K L) :
    (∀ (P : Ideal (integralClosure A L)) [P.IsMaximal]
        [P.LiesOver (maximalIdeal A)],
      @Algebra.IsSeparable (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField P)
        _ _ (Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) P)) ∧
      (∀ (P : Ideal (integralClosure A L)) [P.IsMaximal]
        [P.LiesOver (maximalIdeal A)],
        PrimeToChar (Ideal.ResidueField (maximalIdeal A)) (P.ramificationIdx A)) := sorry
-- Proof strategy: pair `h.residueField_separable_of` with `h.index_primeToChar` at every maximal
-- branch above the base maximal ideal.

/-- Tame ramification is equivalent to residue separability and prime-to-characteristic
ramification indices on all maximal branches. -/
@[stacks 09E9 "tame branch characterization"]
theorem iff_forall :
    IsTamelyRamified A K L ↔
      (∀ (P : Ideal (integralClosure A L)) [P.IsMaximal]
          [P.LiesOver (maximalIdeal A)],
        @Algebra.IsSeparable (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField P)
          _ _ (Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) P)) ∧
        (∀ (P : Ideal (integralClosure A L)) [P.IsMaximal]
          [P.LiesOver (maximalIdeal A)],
          PrimeToChar (Ideal.ResidueField (maximalIdeal A)) (P.ramificationIdx A)) := sorry
-- Proof strategy: use `IsTamelyRamified.spec` forward; backward, construct the class from the
-- residue-separability family and specialize the `PrimeToChar` family to each characteristic
-- prime for `ramificationIdx_coprime`.

end IsTamelyRamified

section

variable {A : Type u} {K : Type v} {L : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

/-- Every unramified DVR field extension is tamely ramified. -/
@[stacks 09E9 "unramified extensions are tame"]
instance IsUnramified.toIsTamelyRamified [IsUnramified A K L] :
    IsTamelyRamified A K L := sorry
-- Proof strategy: construct `IsTamelyRamified`; reuse the unramified residue-field projection,
-- rewrite every branch index to `1`, and discharge coprimality with `Nat.coprime_one_left`.

end

/-- The identity extension of the fraction field is unramified over a DVR. -/
@[stacks 09E9 "unramified identity fraction-field extension"]
instance IsUnramified.of_fractionRing (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] :
    IsUnramified A (FractionRing A) (FractionRing A) := sorry
-- Proof strategy: identify `integralClosure A (FractionRing A)` with `A` using integrally closedness
-- of a DVR; each branch is the base maximal ideal, so the residue map is the identity and its
-- ramification index is `1`.

end DVR.Field
