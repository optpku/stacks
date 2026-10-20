/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.IntermediateField.GeneratorTower

@[expose] public section

universe u v w

open Polynomial

namespace FieldExtension

section

variable {F : Type u} {K : Type v} {L : Type w}
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
variable [Algebra.IsAlgebraic F K]
variable {n : ℕ}

variable (F)
variable (α : Fin n → K)

/-- The base-stage embedding used by the recursive construction of finite-generator stage
embeddings. -/
noncomputable def adjoinStage_zeroEmb :
    adjoinStage F α (0 : Fin (n + 1)) →ₐ[F] L :=
  (Algebra.ofId F L).comp
    (((IntermediateField.equivOfEq (adjoinStage_zero (F := F) α)).trans
      (IntermediateField.botEquiv F K)).toAlgHom)

/-- The concrete recursive data underlying the successive-root predicate. It stores both the
condition accumulated through stage `m` and the resulting embedding of that stage into `L`. -/
noncomputable def successiveRootDataAux (m : ℕ) (hm : m ≤ n)
    (β : Fin n → L) :
    Σ p : Prop, p → adjoinStage F α ⟨m, Nat.lt_succ_of_le hm⟩ →ₐ[F] L := by
  classical
  exact match m with
  | 0 => ⟨True, fun _ ↦ adjoinStage_zeroEmb F α⟩
  | k + 1 =>
      let hk : k ≤ n := Nat.le_of_succ_le hm
      let i : Fin n := ⟨k, Nat.lt_of_succ_le hm⟩
      let prev := successiveRootDataAux k hk β
      let rootProp : Prop :=
        if hp : prev.1 then
          ((minpoly (adjoinStage F α i.castSucc) (α i)).map
            (prev.2 hp).toRingHom).IsRoot (β i)
        else
          False
      ⟨prev.1 ∧ rootProp, fun h ↦
        let hp : prev.1 := h.1
        let ψ := prev.2 hp
        -- Local instance justification (noncanonical choice): the recursively selected preceding stage embedding determines the target algebra structure for this simple-adjoin step.
        letI : Algebra (adjoinStage F α i.castSucc) L := ψ.toRingHom.toAlgebra
        -- Local instance justification (defeq pin): this fixes the scalar tower induced by the chosen preceding-stage embedding while applying the simple-adjoin equivalence.
        letI : IsScalarTower F (adjoinStage F α i.castSucc) L :=
          IsScalarTower.of_algebraMap_eq' (ψ.comp_algebraMap_of_tower F).symm
        let hαi : IsIntegral (adjoinStage F α i.castSucc) (α i) :=
          (Algebra.IsAlgebraic.isAlgebraic
            (R := adjoinStage F α i.castSucc) (α i)).isIntegral
        have hroot :
            ((minpoly (adjoinStage F α i.castSucc) (α i)).map
              ψ.toRingHom).IsRoot (β i) := by
          dsimp [rootProp] at h
          simpa [hp] using h.2
        have hroot' :
            Polynomial.aeval (β i) (minpoly (adjoinStage F α i.castSucc) (α i)) = 0 := by
          change Polynomial.eval₂ ψ.toRingHom (β i)
            (minpoly (adjoinStage F α i.castSucc) (α i)) = 0
          rw [Polynomial.eval₂_eq_eval_map]
          simpa [Polynomial.IsRoot] using hroot
        let ψ' :=
          (IntermediateField.algHomAdjoinIntegralEquiv
            (adjoinStage F α i.castSucc) hαi).symm
              ⟨β i, mem_aroots.mpr ⟨minpoly.ne_zero hαi, hroot'⟩⟩
        (ψ'.restrictScalars F).comp
          (IntermediateField.equivOfEq
            (adjoinStage_succ (F := F) α i)).toAlgHom⟩

/-- The recursive stage data viewed at an arbitrary finite-generator stage. -/
noncomputable def successiveRootData (i : Fin (n + 1))
    (β : Fin n → L) :
    Σ p : Prop, p → adjoinStage F α i →ₐ[F] L := by
  cases i with
  | mk m hm =>
      simpa using successiveRootDataAux F α m (Nat.le_of_lt_succ hm) β

/-- The root condition accumulated through a stage of a finite generator tower. -/
def IsSuccessiveRootTupleUpTo (i : Fin (n + 1)) (β : Fin n → L) : Prop :=
  (successiveRootData F α i β).1

/-- The embedding of a finite-generator stage determined by a tuple satisfying the accumulated
successive-root condition. -/
noncomputable def adjoinStage_emb (i : Fin (n + 1))
    (β : Fin n → L) (hβ : IsSuccessiveRootTupleUpTo F α i β) :
    adjoinStage F α i →ₐ[F] L :=
  (successiveRootData F α i β).2 hβ

/-- The finite-generator stage embedding is independent of the proof of its root condition. -/
theorem adjoinStage_emb_congr {i : Fin (n + 1)} {β : Fin n → L}
    {hβ hβ' : IsSuccessiveRootTupleUpTo F α i β} :
    adjoinStage_emb F α i β hβ =
      adjoinStage_emb F α i β hβ' := sorry

/-- The root condition imposed at one successor stage after its preceding embedding has been
constructed. -/
def IsRootAtStage (i : Fin n) (β : Fin n → L) : Prop :=
  ∀ hβ : IsSuccessiveRootTupleUpTo F α i.castSucc β,
    ((minpoly (adjoinStage F α i.castSucc) (α i)).map
      (adjoinStage_emb F α i.castSucc β hβ).toRingHom).IsRoot (β i)

/-- The initial accumulated root condition is vacuous. -/
@[simp]
theorem isSuccessiveRootTupleUpTo_zero (β : Fin n → L) :
    IsSuccessiveRootTupleUpTo F α 0 β := sorry

/-- The successor accumulated root condition consists of the preceding condition and the next
transported minimal-polynomial root condition. -/
theorem isSuccessiveRootTupleUpTo_succ_iff (i : Fin n) (β : Fin n → L) :
    IsSuccessiveRootTupleUpTo F α i.succ β ↔
      IsSuccessiveRootTupleUpTo F α i.castSucc β ∧
        IsRootAtStage F α i β := sorry

/-- A tuple satisfies the successive-root conditions when it satisfies the accumulated condition
at the full finite-generator stage. -/
abbrev IsSuccessiveRootTuple (β : Fin n → L) : Prop :=
  IsSuccessiveRootTupleUpTo F α (Fin.last n) β

/-- Evaluating an `F`-algebra homomorphism on the generator tuple satisfies the successive-root
conditions. -/
theorem algHom_isSuccessiveRootTuple (φ : K →ₐ[F] L) :
    IsSuccessiveRootTuple F α (φ ∘ α) := sorry

/-- Evaluation of an `F`-algebra homomorphism on a finite generator tuple. -/
def algHom_genTuple (φ : K →ₐ[F] L) : Fin n → L :=
  φ ∘ α

/-- Lemma 9.12.8 (Tag 09H7): when a finite generator tuple spans `K/F`, evaluation identifies
`F`-algebra homomorphisms `K → L` with tuples satisfying the successive-root conditions. -/
theorem algHom_successiveRootTuple_bijective
    (hα : adjoinStage F α (Fin.last n) = ⊤) :
    Function.Bijective
      (fun φ : K →ₐ[F] L ↦
        (⟨algHom_genTuple F α φ, algHom_isSuccessiveRootTuple F α φ⟩ :
          {β : Fin n → L // IsSuccessiveRootTuple F α β})) := sorry

end

end FieldExtension
