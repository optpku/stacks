/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.IntermediateField.GeneratorTower
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.Relrank
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite purely inseparable generator towers

@stack 09HI
-/

universe u v

open scoped IntermediateField

namespace FieldExtension

/-- A finite generator family whose prefix-adjoin stages form successive degree-`p` purely
inseparable simple extensions and generate the full extension. -/
@[stacks 09HI "finite pth-root tower data"]
structure IsPthRootTower (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (p : ℕ) {n : ℕ} (α : Fin n → E) : Prop where
  /-- The full generator family spans the extension field. -/
  stageTop : adjoinStage F α (Fin.last n) = ⊤
  /-- Each successive simple adjunction has relative degree `p`. -/
  relfinrankEq (i : Fin n) :
    (adjoinStage F α (Fin.castSucc i)).relfinrank
      (adjoinStage F α (Fin.succ i)) = p
  /-- Each chosen generator has its `p`th power in the preceding stage. -/
  pthPowerMem (i : Fin n) :
    α i ^ p ∈ adjoinStage F α (Fin.castSucc i)
  /-- No chosen generator is already a `p`th power in the preceding stage. -/
  notPthPower (i : Fin n) :
    ¬ ∃ β : adjoinStage F α (Fin.castSucc i),
      (β : E) ^ p = α i ^ p

/-- The complete stage, degree, power-membership, and non-power conditions of a finite
`p`th-root tower. -/
@[stacks 09HI "finite pth-root tower specification"]
theorem IsPthRootTower.spec
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {p : ℕ} {n : ℕ} {α : Fin n → E} (h : IsPthRootTower F p α) :
    adjoinStage F α (Fin.last n) = ⊤ ∧
      (∀ i : Fin n,
        (adjoinStage F α (Fin.castSucc i)).relfinrank
          (adjoinStage F α (Fin.succ i)) = p) ∧
      (∀ i : Fin n, α i ^ p ∈ adjoinStage F α (Fin.castSucc i)) ∧
      (∀ i : Fin n, ¬ ∃ β : adjoinStage F α (Fin.castSucc i),
        (β : E) ^ p = α i ^ p) :=
  ⟨h.stageTop, h.relfinrankEq, h.pthPowerMem, h.notPthPower⟩

/-- A finite generator family satisfying the complete stage, degree, power-membership,
and non-power conditions forms a finite `p`th-root tower. -/
def IsPthRootTower.ofSpec
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {p : ℕ} {n : ℕ} {α : Fin n → E}
    (h : adjoinStage F α (Fin.last n) = ⊤ ∧
      (∀ i : Fin n,
        (adjoinStage F α (Fin.castSucc i)).relfinrank
          (adjoinStage F α (Fin.succ i)) = p) ∧
      (∀ i : Fin n, α i ^ p ∈ adjoinStage F α (Fin.castSucc i)) ∧
      (∀ i : Fin n, ¬ ∃ β : adjoinStage F α (Fin.castSucc i),
        (β : E) ^ p = α i ^ p)) : IsPthRootTower F p α :=
  { stageTop := h.1
    relfinrankEq := h.2.1
    pthPowerMem := h.2.2.1
    notPthPower := h.2.2.2 }

/-- An extension of degree one has the empty finite `p`th-root tower. -/
private theorem emptyPthRootTowerOfFinrankOne
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (p : ℕ)
    (hKL : Module.finrank K L = 1) :
    ∃ α : Fin 0 → L, IsPthRootTower K p α := by
  refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
  refine
    { stageTop := ?_
      relfinrankEq := ?_
      pthPowerMem := ?_
      notPthPower := ?_ }
  · simpa [adjoinStage, adjoinStage.set] using
      (IntermediateField.bot_eq_top_iff_finrank_eq_one (F := K) (E := L)).2 hKL
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

/-- A degree-`p` simple step strictly decreases the remaining finite extension degree. -/
private theorem finrankTailLtOfDegreePStep
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (p : ℕ) [Fact p.Prime]
    [FiniteDimensional K L] (β : L) (hβ : Module.finrank K K⟮β⟯ = p) :
    Module.finrank K⟮β⟯ L < Module.finrank K L := by
  have hmul : Module.finrank K K⟮β⟯ * Module.finrank K⟮β⟯ L = Module.finrank K L :=
    Module.finrank_mul_finrank K K⟮β⟯ L
  rw [hβ] at hmul
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hpos : 0 < Module.finrank K⟮β⟯ L := Module.finrank_pos
  calc
    Module.finrank K⟮β⟯ L < p * Module.finrank K⟮β⟯ L := by
      simpa [mul_comm] using (lt_mul_of_one_lt_right hpos hp)
    _ = Module.finrank K L := by simpa using hmul

/-- A nontrivial finite purely inseparable extension has a degree-`p` simple step whose
generator becomes a `p`th power in the base but is not already a `p`th power there. -/
theorem existsDegreePSimpleStepOfNontrivial
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] [FiniteDimensional K L] [IsPurelyInseparable K L]
    (hKL : 1 < Module.finrank K L) :
    ∃ β : L,
      Module.finrank K K⟮β⟯ = p ∧
      β ^ p ∈ (⊥ : IntermediateField K L) ∧
      ¬ ∃ γ : (⊥ : IntermediateField K L), (γ : L) ^ p = β ^ p := by
  classical
  have hexpPos : 0 < IsPurelyInseparable.exponent K L := by
    by_contra hexp_zero
    have hexp_zero' : IsPurelyInseparable.exponent K L = 0 := by
      exact le_antisymm (Nat.le_of_not_gt hexp_zero) (Nat.zero_le _)
    have hbot_top : (⊥ : IntermediateField K L) = ⊤ := by
      apply IntermediateField.bot_eq_top_of_finrank_adjoin_eq_one
      intro x
      have hx_range : x ∈ (algebraMap K L).range := by
        simpa [hexp_zero'] using (IsPurelyInseparable.exponent_def' (K := K) (L := L) p x)
      exact (IntermediateField.finrank_adjoin_simple_eq_one_iff (F := K) (E := L) (α := x)).2 <|
        by simpa [IntermediateField.mem_bot] using hx_range
    have hfinrank_one : Module.finrank K L = 1 :=
      (IntermediateField.bot_eq_top_iff_finrank_eq_one (F := K) (E := L)).1 hbot_top
    omega
  have hpred :
      IsPurelyInseparable.exponent K L - 1 < IsPurelyInseparable.exponent K L := by
    omega
  obtain ⟨a, ha_not_range⟩ :=
    IsPurelyInseparable.exponent_min' (K := K) (L := L) p hpred
  let e : ℕ := IsPurelyInseparable.exponent K L
  -- Local instance justification (proof-local temporary data): Frobenius iteration needs the ambient exponent characteristic supplied by the injective base-field map.
  haveI : ExpChar L p := expChar_of_injective_algebraMap (algebraMap K L).injective p
  let β : L := iterateFrobenius L p (e - 1) a
  have hβ_not_bot : β ∉ (⊥ : IntermediateField K L) := by
    simpa [β, e, iterateFrobenius_def, IntermediateField.mem_bot] using ha_not_range
  have he_succ : 1 + (e - 1) = e := by
    omega
  have hβ_pow_mem_range : β ^ p ∈ (algebraMap K L).range := by
    have hpow :
        iterateFrobenius L p e a ∈ (algebraMap K L).range := by
      simpa [e, iterateFrobenius_def] using
        (IsPurelyInseparable.exponent_def' (K := K) (L := L) p a)
    have hfrobenius :
        frobenius L p (iterateFrobenius L p (e - 1) a) = iterateFrobenius L p e a := by
      calc
        frobenius L p (iterateFrobenius L p (e - 1) a)
            = iterateFrobenius L p 1 (iterateFrobenius L p (e - 1) a) := by
                rw [iterateFrobenius_one]
        _ = iterateFrobenius L p (1 + (e - 1)) a := by
              rw [iterateFrobenius_add_apply]
        _ = iterateFrobenius L p e a := by rw [he_succ]
    rw [← hfrobenius] at hpow
    simpa [β, frobenius_def] using hpow
  have hβ_pow_mem_bot : β ^ p ∈ (⊥ : IntermediateField K L) := by
    simpa [IntermediateField.mem_bot] using hβ_pow_mem_range
  have hβ_elemExponent_le_one : IsPurelyInseparable.elemExponent K β ≤ 1 :=
    IsPurelyInseparable.elemExponent_le_of_pow_mem' (K := K) (L := L) p (by
      simpa using hβ_pow_mem_range)
  have hβ_elemExponent_ne_zero : IsPurelyInseparable.elemExponent K β ≠ 0 := by
    intro hzero
    have hβ_range : β ∈ (algebraMap K L).range := by
      simpa [hzero] using (IsPurelyInseparable.elemExponent_def' (K := K) (L := L) p β)
    exact hβ_not_bot <| by simpa [IntermediateField.mem_bot] using hβ_range
  have hβ_elemExponent_one : IsPurelyInseparable.elemExponent K β = 1 := by
    omega
  refine ⟨β, ?_, hβ_pow_mem_bot, ?_⟩
  · rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral β),
      IsPurelyInseparable.minpoly_natDegree_eq' (K := K) (L := L) p β, hβ_elemExponent_one,
      pow_one]
  · rintro ⟨γ, hγ⟩
    have hγ_eq : (γ : L) = β := by
      exact (frobenius L p).injective (by simpa [frobenius_def] using hγ)
    exact hβ_not_bot (show β ∈ (⊥ : IntermediateField K L) from by simpa [hγ_eq] using γ.2)

/-- Restricting the base field of a nested pair of intermediate fields preserves its relative
finite degree. -/
private theorem relfinrankRestrictScalars
    {F : Type u} {K : Type v} {L : Type v} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    (A B : IntermediateField K L) (hAB : A ≤ B) :
    (A.restrictScalars F).relfinrank (B.restrictScalars F) = A.relfinrank B := by
  have hrestrict : A.restrictScalars F ≤ B.restrictScalars F := fun _ hx ↦ hAB hx
  rw [IntermediateField.relfinrank_eq_finrank_of_le hrestrict,
    IntermediateField.relfinrank_eq_finrank_of_le hAB]
  rfl

/-- Strong induction on the extension degree constructs a finite `p`th-root tower. -/
private theorem existsPthRootTowerOfFinitePurelyInseparableAux
    {K : Type v} {L : Type v} [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] [FiniteDimensional K L] [IsPurelyInseparable K L] :
    ∃ (n : ℕ) (α : Fin n → L), IsPthRootTower K p α := by
  generalize hd : Module.finrank K L = d
  induction d using Nat.strongRecOn generalizing K L with
  | ind d ih =>
      by_cases hKL : Module.finrank K L = 1
      · obtain ⟨α, hα⟩ := emptyPthRootTowerOfFinrankOne (K := K) (L := L) p hKL
        exact ⟨0, α, hα⟩
      · have hlt : 1 < Module.finrank K L := by
          have hpos : 0 < Module.finrank K L := Module.finrank_pos
          omega
        obtain ⟨β, hβ_deg, hβ_mem, hβ_not_pth⟩ :=
          existsDegreePSimpleStepOfNontrivial (K := K) (L := L) p hlt
        let M : IntermediateField K L := K⟮β⟯
        have htail : Module.finrank M L < d := by
          rw [← hd]
          simpa [M] using
            finrankTailLtOfDegreePStep (K := K) (L := L) p β hβ_deg
        -- Local instance justification (proof-local temporary data): the recursive base field inherits characteristic `p` from the ambient extension.
        letI : CharP M p := IntermediateField.charP (F := K) (E := L) (L := M) p
        obtain ⟨n, γ, hγ⟩ := ih (Module.finrank M L) htail (K := M) (L := L) rfl
        let α : Fin (n + 1) → L := Fin.cons β γ
        refine ⟨n + 1, α, ?_⟩
        refine
          { stageTop := ?_
            relfinrankEq := ?_
            pthPowerMem := ?_
            notPthPower := ?_ }
        · rw [← Fin.succ_last, adjoinStage_cons_succ (F := K)
            (β := β) (γ := γ) (j := Fin.last n)]
          simpa using congrArg (fun S => S.restrictScalars K) hγ.stageTop
        · intro i
          obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
          · rw [show adjoinStage K α (Fin.castSucc (0 : Fin (n + 1))) = ⊥ by
              simp [α, adjoinStage, adjoinStage.set]]
            rw [show adjoinStage K α (Fin.succ (0 : Fin (n + 1))) = M by
              simpa [α, M] using
                adjoinStage_cons_one (F := K) (β := β) (γ := γ)]
            rw [IntermediateField.relfinrank_bot_left]
            simpa [M] using hβ_deg
          · rw [show adjoinStage K α (Fin.castSucc (Fin.succ j)) =
                (adjoinStage M γ (Fin.castSucc j)).restrictScalars K by
                  simpa [α] using
                    adjoinStage_cons_succ (F := K) (β := β)
                      (γ := γ) (j := Fin.castSucc j)]
            rw [show adjoinStage K α (Fin.succ (Fin.succ j)) =
                (adjoinStage M γ (Fin.succ j)).restrictScalars K by
                  simpa [α] using
                    adjoinStage_cons_succ (F := K) (β := β)
                      (γ := γ) (j := Fin.succ j)]
            have hstages :
                adjoinStage M γ (Fin.castSucc j) ≤ adjoinStage M γ (Fin.succ j) :=
              adjoinStage_mono γ (Nat.le_succ _)
            rw [relfinrankRestrictScalars (F := K) _ _ hstages]
            exact hγ.relfinrankEq j
        · intro i
          obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
          · simpa [α, adjoinStage, adjoinStage.set] using hβ_mem
          · rw [show adjoinStage K α (Fin.castSucc (Fin.succ j)) =
                (adjoinStage M γ (Fin.castSucc j)).restrictScalars K by
                  simpa [α] using
                    adjoinStage_cons_succ (F := K) (β := β)
                      (γ := γ) (j := Fin.castSucc j)]
            simpa [α] using hγ.pthPowerMem j
        · intro i
          obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
          · simpa [α, adjoinStage, adjoinStage.set] using hβ_not_pth
          · rw [show adjoinStage K α (Fin.castSucc (Fin.succ j)) =
                (adjoinStage M γ (Fin.castSucc j)).restrictScalars K by
                  simpa [α] using
                    adjoinStage_cons_succ (F := K) (β := β)
                      (γ := γ) (j := Fin.castSucc j)]
            simpa [α] using hγ.notPthPower j

/-- A finite purely inseparable extension of characteristic `p > 0`
admits a finite family of generators whose successive stages are degree-`p` simple extensions. -/
@[stacks 09HI]
theorem existsPthRootTowerOfFinitePurelyInseparable
    {F : Type u} {E : Type u} [Field F] [Field E] [Algebra F E]
    (p : ℕ) [Fact p.Prime] [CharP F p] [FiniteDimensional F E] [IsPurelyInseparable F E] :
    ∃ (n : ℕ) (α : Fin n → E), IsPthRootTower F p α := by
  simpa using existsPthRootTowerOfFinitePurelyInseparableAux (K := F) (L := E) p

end FieldExtension
