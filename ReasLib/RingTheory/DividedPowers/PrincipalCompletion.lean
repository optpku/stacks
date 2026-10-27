/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

/-- Applying divided powers to representatives at precision `e + offset` gives a
well-defined result at precision `e`, since `(p) ^ offset ≤ J`. -/
theorem dpowStage_sound
    {B : Type u} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p offset : ℕ)
    (hpow : Ideal.span {(p : B)} ^ offset ≤ J) (n e : ℕ) {x y : B}
    (h : (Ideal.span {(p : B)} ^ (e + offset) • (⊤ : Submodule B B)).quotientRel x y) :
    (Submodule.Quotient.mk (δ.dpow n x) :
        B ⧸ (Ideal.span {(p : B)} ^ e • (⊤ : Submodule B B))) =
      Submodule.Quotient.mk (δ.dpow n y) := sorry

/-- The operation `[b] ↦ [δₙ(b)]`, from precision `e + offset` to precision `e`.
It is defined by quotient descent, without selecting a representative. -/
noncomputable def dpowStage
    {B : Type u} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p offset : ℕ)
    (hpow : Ideal.span {(p : B)} ^ offset ≤ J) (n e : ℕ)
    (x : B ⧸ (Ideal.span {(p : B)} ^ (e + offset) • (⊤ : Submodule B B))) :
    B ⧸ (Ideal.span {(p : B)} ^ e • (⊤ : Submodule B B)) :=
  Quotient.liftOn' x (fun b ↦ Submodule.Quotient.mk (δ.dpow n b)) fun _ _ h ↦
    dpowStage_sound δ p offset hpow n e h

/-- The quotient operations commute with reduction to lower precision. -/
theorem dpowStage_compat
    {B : Type u} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p offset : ℕ)
    (hpow : Ideal.span {(p : B)} ^ offset ≤ J) (n : ℕ)
    (x : AdicCompletion (Ideal.span {(p : B)}) B) {e f : ℕ} (h : e ≤ f) :
    AdicCompletion.transitionMap (Ideal.span {(p : B)}) B h
        (dpowStage δ p offset hpow n f (x.val (f + offset))) =
      dpowStage δ p offset hpow n e (x.val (e + offset)) := sorry

/-- The continuous extension, assembled from its explicit compatible quotient coordinates. -/
noncomputable def completedDpow
    {B : Type u} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p offset : ℕ)
    (hpow : Ideal.span {(p : B)} ^ offset ≤ J) (n : ℕ)
    (x : AdicCompletion (Ideal.span {(p : B)}) B) :
    AdicCompletion (Ideal.span {(p : B)}) B :=
  ⟨fun e ↦ dpowStage δ p offset hpow n e (x.val (e + offset)),
    fun h ↦ dpowStage_compat δ p offset hpow n x h⟩

/-- The completed divided-power structure, with operations defined coordinatewise by
quotient descent from the original divided powers. -/
noncomputable def powers
    {B : Type u} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p offset : ℕ)
    (hpow : Ideal.span {(p : B)} ^ offset ≤ J) :
    DividedPowers
      (RingHom.ker (AdicCompletion.toQuotient
        (Ideal.span {(p : B)}) J offset hpow)) :=
  { dpow := completedDpow δ p offset hpow
    dpow_null := sorry
    dpow_zero := sorry
    dpow_one := sorry
    dpow_mem := sorry
    dpow_add := sorry
    dpow_mul := sorry
    mul_dpow := sorry
    dpow_comp := sorry }

/-- The completed operation at precision `e` is the original operation at precision
`e + offset`, reduced to precision `e`. -/
theorem powers_dpow_val
    {B : Type u} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p offset : ℕ)
    (hpow : Ideal.span {(p : B)} ^ offset ≤ J) (n e : ℕ)
    (x : AdicCompletion (Ideal.span {(p : B)}) B) :
    ((powers δ p offset hpow).dpow n x).val e =
      dpowStage δ p offset hpow n e (x.val (e + offset)) := rfl

/-- The completed divided powers extend the original ones along the completion map. -/
theorem powers_isDPMorphism
    {B : Type u} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p offset : ℕ)
    (hpow : Ideal.span {(p : B)} ^ offset ≤ J) :
    IsDPMorphism δ (powers δ p offset hpow)
      (algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B)) := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change AdicCompletion.toQuotient (Ideal.span {(p : B)}) J offset hpow
      (algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B) b) = 0
    have hcomp := congrArg (fun f : B →+* B ⧸ J ↦ f b)
      (AdicCompletion.toQuotient_comp_algebraMap
        (Ideal.span {(p : B)}) J offset hpow)
    rw [RingHom.comp_apply] at hcomp
    rw [hcomp]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
  · intro n b _
    apply Subtype.ext
    funext e
    rfl

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
