/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Sequential.ModNsmul
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf

/-!
# Eventual values of reduced ℓ-adic systems

The stages are limits of the actual quotient systems. Their transition maps are
induced by the canonical quotient reductions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

open CategoryTheory.SequentialInverseSystem
open CategoryTheory.Limits

variable {X : Scheme.{u}}
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- The inverse-limit value of the reduced tower `G / ℓ^{k+1} G`. -/
def eventualFamily
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (ℓ k : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  limit (G.modNsmulSystem ℓ k)

/-- The successor map of eventual values induced by reducing `ℓ^{k+2}` to `ℓ^{k+1}`. -/
def eventualStepMap
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (ℓ k : ℕ) :
    eventualFamily G ℓ (k + 1) ⟶ eventualFamily G ℓ k :=
  limMap (G.modNsmulReduce ℓ k)

/-- The inverse system whose stage `k` is the inverse limit of `G / ℓ^{k+1} G`. -/
def eventualSystem
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (ℓ : ℕ) :
    SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  Functor.ofOpSequence (eventualStepMap G ℓ)

/-- Stage `k` of the eventual system is the limit of the `ℓ^{k+1}`-reduced tower. -/
theorem eventualSystem_obj
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (ℓ k : ℕ) :
    (eventualSystem G ℓ).family k = limit (G.modNsmulSystem ℓ k) := rfl

private theorem eventualReduction_isKilled {C : Type*} [Category* C] [Preadditive C]
    [HasCokernels C] (Y : C) (b : ℕ) :
    b • 𝟙 (nsmulCokernel Y b) = 0 := by
  apply (cancel_epi (cokernel.π (b • 𝟙 Y))).1
  simpa only [comp_nsmul, nsmul_comp, Category.comp_id, Category.id_comp, comp_zero]
    using cokernel.condition (b • 𝟙 Y)

private theorem eventualReduction_isAdic {C : Type*} [Category* C] [Preadditive C]
    [HasCokernels C] (Y : C) (m b : ℕ)
    (h : (b • 𝟙 (nsmulCokernel Y (b * m))) ≫ nsmulCokernelReduce Y m b = 0) :
    IsIso (cokernel.desc (b • 𝟙 (nsmulCokernel Y (b * m)))
      (nsmulCokernelReduce Y m b) h) := by
  let p := cokernel.π ((b * m) • 𝟙 Y)
  have hdesc : (b • 𝟙 Y) ≫ p ≫ cokernel.π (b • 𝟙 (nsmulCokernel Y (b * m))) = 0 := by
    calc
      _ = p ≫ (b • 𝟙 (nsmulCokernel Y (b * m))) ≫
          cokernel.π (b • 𝟙 (nsmulCokernel Y (b * m))) := by
        simp only [nsmul_comp, comp_nsmul, Category.id_comp]
      _ = 0 := by rw [cokernel.condition, comp_zero]
  let i := cokernel.desc (b • 𝟙 Y)
    (p ≫ cokernel.π (b • 𝟙 (nsmulCokernel Y (b * m)))) hdesc
  refine ⟨i, ?_, ?_⟩
  · apply (cancel_epi (cokernel.π (b • 𝟙 (nsmulCokernel Y (b * m))))).1
    apply (cancel_epi p).1
    simp [i, p, nsmulCokernelReduce]
  · apply (cancel_epi (cokernel.π (b • 𝟙 Y))).1
    simp [i, p, nsmulCokernelReduce, Category.assoc]

private theorem eventualFamily_isKilled
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (ℓ k : ℕ) :
    (ℓ ^ (k + 1)) • 𝟙 (eventualFamily G ℓ k) = 0 := by
  change (ℓ ^ (k + 1)) • 𝟙 (limit (G.modNsmulSystem ℓ k)) = 0
  apply limit.hom_ext
  intro j
  have h : (ℓ ^ (k + 1)) • 𝟙 ((G.modNsmulSystem ℓ k).obj j) = 0 :=
    eventualReduction_isKilled (G.obj j) (ℓ ^ (k + 1))
  simpa only [nsmul_comp, comp_nsmul, Category.id_comp, Category.comp_id, zero_comp,
    comp_zero] using congrArg (fun f ↦ limit.π (G.modNsmulSystem ℓ k) j ≫ f) h

private theorem eventualStepMap_isAdic
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (ℓ n : ℕ) (h : G.IsEventuallyConstantModNsmul ℓ)
    (hstep : ((ℓ ^ (n + 1)) • 𝟙 (eventualFamily G ℓ (n + 1))) ≫
      eventualStepMap G ℓ n = 0) :
    IsIso (cokernel.desc ((ℓ ^ (n + 1)) • 𝟙 (eventualFamily G ℓ (n + 1)))
      (eventualStepMap G ℓ n) hstep) := by
  obtain ⟨N₀, h₀⟩ := h n
  obtain ⟨N₁, h₁⟩ := h (n + 1)
  let N := max N₀ N₁
  let p : eventualFamily G ℓ (n + 1) ⟶
      nsmulCokernel (G.family N) (ℓ ^ (n + 1) * ℓ) :=
    limit.π (G.modNsmulSystem ℓ (n + 1)) (op N)
  let q : eventualFamily G ℓ n ⟶ nsmulCokernel (G.family N) (ℓ ^ (n + 1)) :=
    limit.π (G.modNsmulSystem ℓ n) (op N)
  haveI : IsIso p := h₁.isIso_π_of_isLimit'
    (limit.isLimit (G.modNsmulSystem ℓ (n + 1))) (op N) (homOfLE (le_max_right N₀ N₁)).op
  haveI : IsIso q := h₀.isIso_π_of_isLimit'
    (limit.isLimit (G.modNsmulSystem ℓ n)) (op N) (homOfLE (le_max_left N₀ N₁)).op
  let r := nsmulCokernelReduce (G.family N) ℓ (ℓ ^ (n + 1))
  have hr : ((ℓ ^ (n + 1)) • 𝟙 (nsmulCokernel (G.family N) (ℓ ^ (n + 1) * ℓ))) ≫ r = 0 := by
    calc
      _ = r ≫ ((ℓ ^ (n + 1)) • 𝟙 (nsmulCokernel (G.family N) (ℓ ^ (n + 1)))) := by
        simp
      _ = 0 := by rw [eventualReduction_isKilled, comp_zero]
  haveI : IsIso (cokernel.desc
      ((ℓ ^ (n + 1)) • 𝟙 (nsmulCokernel (G.family N) (ℓ ^ (n + 1) * ℓ))) r hr) :=
    eventualReduction_isAdic (G.family N) ℓ (ℓ ^ (n + 1)) hr
  let c := nsmulCokernelMap (ℓ ^ (n + 1)) p
  haveI : IsIso c := by
    dsimp only [c, nsmulCokernelMap]
    infer_instance
  have hcomm : eventualStepMap G ℓ n ≫ q = p ≫ r := by
    change limMap (G.modNsmulReduce ℓ n) ≫ limit.π (G.modNsmulSystem ℓ n) (op N) =
      limit.π (G.modNsmulSystem ℓ (n + 1)) (op N) ≫ (G.modNsmulReduce ℓ n).app (op N)
    exact limMap_π (G.modNsmulReduce ℓ n) (op N)
  have hfac : cokernel.desc _ (eventualStepMap G ℓ n) hstep ≫ q =
      c ≫ cokernel.desc _ r hr := by
    apply (cancel_epi (cokernel.π ((ℓ ^ (n + 1)) • 𝟙 (eventualFamily G ℓ (n + 1))))).1
    simpa [c, nsmulCokernelMap, Category.assoc] using hcomm
  haveI : IsIso (cokernel.desc _ (eventualStepMap G ℓ n) hstep ≫ q) := by
    rw [hfac]
    infer_instance
  exact IsIso.of_isIso_comp_right _ q

variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]

/-- The `ℤ_[ℓ]`-sheaf whose stages are the eventual values of the reduced towers of `G`. -/
def ofEventuallyConstant
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h_killed : ∀ n, (ℓ ^ (n + 1)) • 𝟙 (G.family n) = 0)
    (h_constructible :
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F) (G.family n))
    (h_eventuallyConstant : G.IsEventuallyConstantModNsmul ℓ) :
    ZEllSheaf X ℓ :=
  ofSystem (eventualSystem G ℓ)
    (by
      intro n
      exact eventualFamily_isKilled G ℓ n)
    (by
      intro n
      calc
        ((ℓ ^ (n + 1)) • 𝟙 _) ≫ (eventualSystem G ℓ).stepMap n =
            (eventualSystem G ℓ).stepMap n ≫ ((ℓ ^ (n + 1)) • 𝟙 _) := by
          simp
        _ = 0 := by
          rw [show (ℓ ^ (n + 1)) • 𝟙 ((eventualSystem G ℓ).family n) = 0 from
            eventualFamily_isKilled G ℓ n, comp_zero])
    (by
      intro n
      change IsIso (cokernel.desc _ ((Functor.ofOpSequence (eventualStepMap G ℓ)).map
        (homOfLE (Nat.le_add_right n 1)).op) _)
      simp only [Functor.ofOpSequence_map_homOfLE_succ]
      exact eventualStepMap_isAdic G ℓ n h_eventuallyConstant _)
    (by sorry)

/-- Stages of `ofEventuallyConstant` are the stages of `eventualSystem`. -/
theorem ofEventuallyConstant_stage
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h_killed : ∀ n, (ℓ ^ (n + 1)) • 𝟙 (G.family n) = 0)
    (h_constructible :
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F) (G.family n))
    (h_eventuallyConstant : G.IsEventuallyConstantModNsmul ℓ) (k : ℕ) :
    (ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).stage k =
      (eventualSystem G ℓ).family k := rfl

/-- The source component `F_k` is stage `k-1` of `ofEventuallyConstant`. -/
theorem ofEventuallyConstant_component
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h_killed : ∀ n, (ℓ ^ (n + 1)) • 𝟙 (G.family n) = 0)
    (h_constructible :
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F) (G.family n))
    (h_eventuallyConstant : G.IsEventuallyConstantModNsmul ℓ) (k : ℕ+) :
    (ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).component k =
      (eventualSystem G ℓ).family k.natPred := rfl

/-- Stage `k` of the constructed sheaf is an eventual value of `G / ℓ^{k+1} G`. -/
theorem ofEventuallyConstant_isEventuallyConstantWithValue
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h_killed : ∀ n, (ℓ ^ (n + 1)) • 𝟙 (G.family n) = 0)
    (h_constructible :
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F) (G.family n))
    (h_eventuallyConstant : G.IsEventuallyConstantModNsmul ℓ) (k : ℕ) :
    (G.modNsmulSystem ℓ k).IsEventuallyConstantWithValue
      ((ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).stage k) := by
  obtain ⟨N, hN⟩ := h_eventuallyConstant k
  haveI : IsIso (limit.π (G.modNsmulSystem ℓ k) (op N)) :=
    hN.isIso_π_of_isLimit (limit.isLimit (G.modNsmulSystem ℓ k))
  exact ⟨N, hN, ⟨(asIso (limit.π (G.modNsmulSystem ℓ k) (op N))).symm⟩⟩

/-- Late projections from the reduced system to its inverse limit are isomorphisms. -/
theorem isIso_limit_π
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h_eventuallyConstant : G.IsEventuallyConstantModNsmul ℓ) (k : ℕ) :
    ∃ N, ∀ n, N ≤ n → IsIso (limit.π (G.modNsmulSystem ℓ k) (op n)) := by
  obtain ⟨N, hN⟩ := h_eventuallyConstant k
  refine ⟨N, fun n hn ↦ ?_⟩
  exact hN.isIso_π_of_isLimit' (limit.isLimit (G.modNsmulSystem ℓ k))
    (op n) (homOfLE hn).op

/-- The constructed inverse system is killed by `ℓ^{n+1}`, adic, and constructible. -/
theorem ofEventuallyConstant_spec
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h_killed : ∀ n, (ℓ ^ (n + 1)) • 𝟙 (G.family n) = 0)
    (h_constructible :
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F) (G.family n))
    (h_eventuallyConstant : G.IsEventuallyConstantModNsmul ℓ) :
    (∀ n, (ℓ ^ (n + 1)) • 𝟙
        ((ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).stage n) = 0) ∧
      (∀ n, IsIso
        ((ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).adicCokernel n)) ∧
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F)
        ((ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).stage n) := by
  let F := ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant
  exact ⟨F.isKilled, F.isAdic, F.isConstructible⟩

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
