/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy
public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Product
public import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Data.Fintype.Basic

/-!
# Products of simplicial homotopies

Directed simplicial homotopies combine componentwise over arbitrary categorical products. The
induced zigzag homotopy relation is closed under products indexed by a finite type.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SimplexCategory Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable {T : Type w}

namespace Homotopy

variable {X Y : T → SimplicialObject C}
variable [FunctorCategory.HasPointwiseProduct X]
variable [FunctorCategory.HasPointwiseProduct Y]
variable {a b : ∀ t, X t ⟶ Y t}

/-- The degreewise component of the product of a family of directed simplicial homotopies. -/
@[stacks 08Q4 "degreewise product homotopy component"]
def piMapComponent (H : ∀ t, Homotopy (a t) (b t)) {n : ℕ} (i : Fin (n + 1)) :
    (∏ᶜ X) _⦋n⦌ ⟶ (∏ᶜ Y) _⦋n + 1⦌ :=
  (FunctorCategory.evaluation.piIso X (op ⦋n⦌)).hom ≫
    Limits.Pi.map (fun t ↦ (H t).h i) ≫
    (FunctorCategory.evaluation.piIso Y (op ⦋n + 1⦌)).inv

namespace piMapComponent

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_hom_π (F : T → SimplicialObject C)
    [FunctorCategory.HasPointwiseProduct F] (k : SimplexCategoryᵒᵖ) (t : T) :
    (FunctorCategory.evaluation.piIso F k).hom ≫
      Limits.Pi.π (fun t ↦ (F t).obj k) t = (Limits.Pi.π F t).app k := by
  simp only [FunctorCategory.evaluation.piIso, FunctorCategory.evaluation.limitIso,
    Iso.trans_hom, Category.assoc, Limits.Pi.π, HasLimit.isoOfNatIso_hom_π,
    Discrete.compNatIsoDiscrete_hom_app]
  exact (congrArg
    (fun f ↦ (preservesLimitIso ((evaluation SimplexCategoryᵒᵖ C).obj k)
      (Discrete.functor F)).hom ≫ f) (Category.comp_id _)).trans
        (preservesLimitIso_hom_π _ _ _)

private theorem evaluation_inv_π (F : T → SimplicialObject C)
    [FunctorCategory.HasPointwiseProduct F] (k : SimplexCategoryᵒᵖ) (t : T) :
    (FunctorCategory.evaluation.piIso F k).inv ≫ (Limits.Pi.π F t).app k =
      Limits.Pi.π (fun t ↦ (F t).obj k) t := by
  rw [Iso.inv_comp_eq]
  exact (evaluation_hom_π F k t).symm

private theorem evaluated_hom_ext (F : T → SimplicialObject C)
    [FunctorCategory.HasPointwiseProduct F] (k : SimplexCategoryᵒᵖ)
    {W : C} {f g : W ⟶ (∏ᶜ F).obj k}
    (h : ∀ t, f ≫ (Limits.Pi.π F t).app k = g ≫ (Limits.Pi.π F t).app k) :
    f = g := by
  apply (cancel_mono (FunctorCategory.evaluation.piIso F k).hom).1
  apply Limits.Pi.hom_ext
  intro t
  simpa only [Category.assoc, evaluation_hom_π] using h t

@[reassoc]
private theorem projection (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i : Fin (n + 1)) (t : T) :
    piMapComponent H i ≫ (Limits.Pi.π Y t).app (op ⦋n + 1⦌) =
      (Limits.Pi.π X t).app (op ⦋n⦌) ≫ (H t).h i := by
  simp only [piMapComponent, Category.assoc, evaluation_inv_π, Limits.Pi.map_π]
  rw [← Category.assoc, evaluation_hom_π]

/-- The product component has the required zero endpoint. -/
@[stacks 08Q4 "product homotopy zero endpoint"]
theorem zero (H : ∀ t, Homotopy (a t) (b t)) (n : ℕ) :
    piMapComponent H (0 : Fin (n + 1)) ≫ (∏ᶜ Y).δ 0 =
      (Limits.Pi.map b).app (op ⦋n⦌) := by
  apply evaluated_hom_ext Y (op ⦋n⦌)
  intro t
  simp only [Category.assoc, δ_naturality, projection_assoc,
    h_zero_comp_δ_zero, ← NatTrans.comp_app, Limits.Pi.map_π]

/-- The product component has the required last endpoint. -/
@[stacks 08Q4 "product homotopy last endpoint"]
theorem last (H : ∀ t, Homotopy (a t) (b t)) (n : ℕ) :
    piMapComponent H (Fin.last n) ≫ (∏ᶜ Y).δ (Fin.last (n + 1)) =
      (Limits.Pi.map a).app (op ⦋n⦌) := by
  apply evaluated_hom_ext Y (op ⦋n⦌)
  intro t
  simp only [Category.assoc, δ_naturality, projection_assoc,
    h_last_comp_δ_last, ← NatTrans.comp_app, Limits.Pi.map_π]

/-- Product components satisfy the first face relation. -/
@[stacks 08Q4 "product homotopy first face relation"]
theorem face_of_le (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    piMapComponent H j.succ ≫ (∏ᶜ Y).δ i.castSucc =
      (∏ᶜ X).δ i ≫ piMapComponent H j := by
  apply evaluated_hom_ext Y (op ⦋n + 1⦌)
  intro t
  simp only [Category.assoc, δ_naturality, δ_naturality_assoc, projection,
    projection_assoc, h_succ_comp_δ_castSucc_of_lt _ i j hij]

/-- Product components satisfy the adjacent-face relation. -/
@[stacks 08Q4 "product homotopy adjacent face relation"]
theorem face_adjacent (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (j : Fin (n + 1)) :
    piMapComponent H j.succ ≫ (∏ᶜ Y).δ j.castSucc.succ =
      piMapComponent H j.castSucc ≫ (∏ᶜ Y).δ j.castSucc.succ := by
  apply evaluated_hom_ext Y (op ⦋n + 1⦌)
  intro t
  simp only [Category.assoc, δ_naturality, projection_assoc,
    h_succ_comp_δ_castSucc_succ]

/-- Product components satisfy the complementary face relation. -/
@[stacks 08Q4 "product homotopy complementary face relation"]
theorem face_of_lt (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    piMapComponent H j.castSucc ≫ (∏ᶜ Y).δ i.succ =
      (∏ᶜ X).δ i ≫ piMapComponent H j := by
  apply evaluated_hom_ext Y (op ⦋n + 1⦌)
  intro t
  simp only [Category.assoc, δ_naturality, δ_naturality_assoc, projection,
    projection_assoc, h_castSucc_comp_δ_succ_of_lt _ i j hji]

/-- Product components satisfy the first degeneracy relation. -/
@[stacks 08Q4 "product homotopy first degeneracy relation"]
theorem degeneracy_of_le (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    piMapComponent H j ≫ (∏ᶜ Y).σ i.castSucc =
      (∏ᶜ X).σ i ≫ piMapComponent H j.succ := by
  apply evaluated_hom_ext Y (op ⦋n + 2⦌)
  intro t
  simp only [Category.assoc, σ_naturality, σ_naturality_assoc, projection,
    projection_assoc, h_comp_σ_castSucc_of_le _ i j hij]

/-- Product components satisfy the complementary degeneracy relation. -/
@[stacks 08Q4 "product homotopy complementary degeneracy relation"]
theorem degeneracy_of_lt (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    piMapComponent H j ≫ (∏ᶜ Y).σ i.succ =
      (∏ᶜ X).σ i ≫ piMapComponent H j.castSucc := by
  apply evaluated_hom_ext Y (op ⦋n + 2⦌)
  intro t
  simp only [Category.assoc, σ_naturality, σ_naturality_assoc, projection,
    projection_assoc, h_comp_σ_succ_of_lt _ i j hji]

end piMapComponent

/-- A family of directed simplicial homotopies induces a directed homotopy between the product
maps. -/
@[stacks 08Q4 "products of simplicial homotopies"]
def piMap (H : ∀ t, Homotopy (a t) (b t)) :
    Homotopy (Limits.Pi.map a) (Limits.Pi.map b) where
  h := piMapComponent H
  h_zero_comp_δ_zero := piMapComponent.zero H
  h_last_comp_δ_last := piMapComponent.last H
  h_succ_comp_δ_castSucc_of_lt := piMapComponent.face_of_le H
  h_succ_comp_δ_castSucc_succ := piMapComponent.face_adjacent H
  h_castSucc_comp_δ_succ_of_lt := piMapComponent.face_of_lt H
  h_comp_σ_castSucc_of_le := piMapComponent.degeneracy_of_le H
  h_comp_σ_succ_of_lt := piMapComponent.degeneracy_of_lt H

namespace piMap

/-- The homotopy components of `piMap H` are the canonical pointwise product components. -/
@[simp, stacks 08Q4 "product homotopy component formula"]
theorem h (H : ∀ t, Homotopy (a t) (b t)) {n : ℕ} (i : Fin (n + 1)) :
    (piMap H).h i = piMapComponent H i := rfl

end piMap

end Homotopy

namespace DirectedHomotopy

variable {X Y : T → SimplicialObject C}
variable [FunctorCategory.HasPointwiseProduct X]
variable [FunctorCategory.HasPointwiseProduct Y]
variable {a b : ∀ t, X t ⟶ Y t}

/-- Products preserve a family of directed simplicial-homotopy relations.  Unlike the zigzag
closure, this statement does not require the index type to be finite. -/
@[stacks 08Q4 "products preserve directed simplicial homotopy"]
theorem piMap (hab : ∀ t, DirectedHomotopy (a t) (b t)) :
    DirectedHomotopy (Limits.Pi.map a) (Limits.Pi.map b) := by
  exact ⟨Homotopy.piMap (fun t ↦ Classical.choice (hab t))⟩

end DirectedHomotopy

namespace Homotopic

variable [Finite T]
variable {X Y : T → SimplicialObject C}
variable [FunctorCategory.HasPointwiseProduct X]
variable [FunctorCategory.HasPointwiseProduct Y]
variable {a b : ∀ t, X t ⟶ Y t}

/-- A finite family of zigzag simplicial homotopies induces a zigzag homotopy between the product
maps. -/
@[stacks 08Q4 "finite products preserve simplicial homotopy"]
theorem piMap (hab : ∀ t, Homotopic (a t) (b t)) :
    Homotopic (Limits.Pi.map a) (Limits.Pi.map b) := by
  classical
  letI := Fintype.ofFinite T
  have single (c : ∀ t, X t ⟶ Y t) (t : T) {f g : X t ⟶ Y t}
      (hfg : Homotopic f g) :
      Homotopic (Limits.Pi.map (Function.update c t f))
        (Limits.Pi.map (Function.update c t g)) := by
    induction hfg with
    | rel f g hfg =>
      apply Relation.EqvGen.rel
      apply DirectedHomotopy.piMap
      intro s
      by_cases hst : s = t
      · subst s
        simpa only [Function.update_self] using hfg
      · simpa only [Function.update_of_ne hst, DirectedHomotopy] using
          (⟨Homotopy.refl (c s)⟩ : DirectedHomotopy (c s) (c s))
    | refl f => exact Relation.EqvGen.refl _
    | symm f g _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans f g h _ _ hfg hgh => exact Relation.EqvGen.trans _ _ _ hfg hgh
  have finite_step (s : Finset T) :
      Homotopic (Limits.Pi.map a)
        (Limits.Pi.map (fun t ↦ if t ∈ s then b t else a t)) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa [Homotopic] using Relation.EqvGen.refl (r := DirectedHomotopy) (Limits.Pi.map a)
    | @insert t s hts ih =>
      let c : ∀ t, X t ⟶ Y t := fun t ↦ if t ∈ s then b t else a t
      have ha : Function.update c t (a t) = c := by
        apply Function.update_eq_self_iff.mpr
        simp [c, hts]
      have hb : Function.update c t (b t) =
          (fun i ↦ if i ∈ insert t s then b i else a i) := by
        funext i
        by_cases hit : i = t
        · subst i
          simp
        · simp [c, hit]
      exact Relation.EqvGen.trans _ _ _ ih
        (by simpa only [ha, hb, Homotopic] using single c t (hab t))
  simpa using finite_step Finset.univ

end Homotopic

end CategoryTheory.SimplicialObject
