/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.AdicCompletion

@[expose] public section

universe u

namespace DividedPowers.PrincipalCompletion

/- The index is computed from the nilpotence witness supplied by the quotient. -/
/-- The least exponent witnessing nilpotence of `p` in `B ⧸ J`. -/
noncomputable def nilpotenceIndex
    {B : Type u} [CommRing B] {J : Ideal B} (p : ℕ)
    (h_nilpotent : IsNilpotent (p : B ⧸ J)) : ℕ :=
  -- Local instance justification (proof-local temporary data): `Nat.find` needs a decidability witness for the quotient nilpotence predicate.
  letI := Classical.decPred (fun n : ℕ ↦ (p : B ⧸ J) ^ n = 0)
  Nat.find h_nilpotent

/-- The nilpotence index satisfies the defining quotient equation. -/
theorem nilpotenceIndex_spec
    {B : Type u} [CommRing B] {J : Ideal B} (p : ℕ)
    (h_nilpotent : IsNilpotent (p : B ⧸ J)) :
    ((p : B ⧸ J) ^ nilpotenceIndex p h_nilpotent) = 0 := sorry

/-- A deterministic stable-tail offset attached to the nilpotence index. -/
noncomputable def stableOffset
    {B : Type u} [CommRing B] {J : Ideal B} (p : ℕ)
    (h_nilpotent : IsNilpotent (p : B ⧸ J)) : ℕ :=
  2 * (nilpotenceIndex p h_nilpotent + 1)

/-- The stable offset is strictly beyond the nilpotence index. -/
theorem stableOffset_spec
    {B : Type u} [CommRing B] {J : Ideal B} (p : ℕ)
    (h_nilpotent : IsNilpotent (p : B ⧸ J)) :
    nilpotenceIndex p h_nilpotent < stableOffset p h_nilpotent := sorry

/- The two facts below package the eventual-stability input needed by the
   quotient-power tower.  They are proof-valued; the offset itself remains
   the explicit deterministic datum above. -/
/-- The principal power at the stable offset is contained in the divided-power ideal. -/
theorem stableOffset_pow_le
    {B : Type u} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p : ℕ)
    (h_nilpotent : IsNilpotent (p : B ⧸ J)) :
    Ideal.span {(p : B)} ^ stableOffset p h_nilpotent ≤ J := sorry

/-- Divided powers are stable on all principal powers from the chosen offset onward. -/
theorem stableOffset_isStable
    {B : Type u} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p : ℕ)
    (h_nilpotent : IsNilpotent (p : B ⧸ J)) :
    δ.IsStableUnderPowers (Ideal.span {(p : B)}) (stableOffset p h_nilpotent) := sorry

/-- The completed divided-power structure supplied by the principal-adic extension theorem. -/
noncomputable def powers
    {B : Type u} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p offset : ℕ)
    (hpow : Ideal.span {(p : B)} ^ offset ≤ J) :
    DividedPowers
      (RingHom.ker (AdicCompletion.toQuotient
        (Ideal.span {(p : B)}) J offset hpow)) :=
  Classical.choose (DividedPowers.exists_principalCompletionExtension
    δ p offset hpow)

/-- The completed divided powers extend the original ones along the completion map. -/
theorem powers_isDPMorphism
    {B : Type u} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p offset : ℕ)
    (hpow : Ideal.span {(p : B)} ^ offset ≤ J) :
    IsDPMorphism δ (powers δ p offset hpow)
      (algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B)) :=
  (Classical.choose_spec (DividedPowers.exists_principalCompletionExtension
    δ p offset hpow))

/-- The completed divided powers are uniquely determined by their extension property. -/
theorem powers_unique
    {B : Type u} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p offset : ℕ)
    (hpow : Ideal.span {(p : B)} ^ offset ≤ J)
    {γhat : DividedPowers
      (RingHom.ker (AdicCompletion.toQuotient
        (Ideal.span {(p : B)}) J offset hpow))}
    (hγhat : IsDPMorphism δ γhat
      (algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B))) :
    γhat = powers δ p offset hpow := sorry

end DividedPowers.PrincipalCompletion
