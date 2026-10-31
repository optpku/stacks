/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy
public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Coproduct
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coproducts of simplicial homotopies

Directed simplicial homotopies combine componentwise over arbitrary categorical coproducts. The
induced zigzag homotopy relation is closed under coproducts indexed by a finite type.
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
variable [FunctorCategory.HasPointwiseCoproduct X]
variable [FunctorCategory.HasPointwiseCoproduct Y]
variable {a b : ∀ t, X t ⟶ Y t}

/-- The degreewise component of the coproduct of a family of directed simplicial homotopies. -/
@[stacks 08Q4 "degreewise coproduct homotopy component"]
def sigmaMapComponent (H : ∀ t, Homotopy (a t) (b t)) {n : ℕ} (i : Fin (n + 1)) :
    (∐ X) _⦋n⦌ ⟶ (∐ Y) _⦋n + 1⦌ :=
  (FunctorCategory.evaluation.sigmaIso X (op ⦋n⦌)).hom ≫
    Limits.Sigma.map (fun t ↦ (H t).h i) ≫
    (FunctorCategory.evaluation.sigmaIso Y (op ⦋n + 1⦌)).inv

namespace sigmaMapComponent

set_option backward.isDefEq.respectTransparency false in
private theorem ι_sigmaIso_hom (F : T → SimplicialObject C)
    [FunctorCategory.HasPointwiseCoproduct F] (k : SimplexCategoryᵒᵖ) (t : T) :
    (Limits.Sigma.ι F t).app k ≫ (FunctorCategory.evaluation.sigmaIso F k).hom =
      Limits.Sigma.ι (fun t ↦ (F t).obj k) t := by
  change ((evaluation _ _).obj k).map (colimit.ι (Discrete.functor F) ⟨t⟩) ≫ _ = _
  simp only [FunctorCategory.evaluation.sigmaIso, FunctorCategory.evaluation.colimitIso,
    Iso.trans_hom, ι_preservesColimitIso_hom_assoc, HasColimit.isoOfNatIso_ι_hom,
    Discrete.compNatIsoDiscrete_hom_app]
  exact Category.id_comp (Limits.Sigma.ι (fun t ↦ (F t).obj k) t)

private theorem ι_sigmaIso_inv (F : T → SimplicialObject C)
    [FunctorCategory.HasPointwiseCoproduct F] (k : SimplexCategoryᵒᵖ) (t : T) :
    Limits.Sigma.ι (fun t ↦ (F t).obj k) t ≫
        (FunctorCategory.evaluation.sigmaIso F k).inv = (Limits.Sigma.ι F t).app k := by
  rw [← ι_sigmaIso_hom F k t, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem app_hom_ext (F : T → SimplicialObject C)
    [FunctorCategory.HasPointwiseCoproduct F] (k : SimplexCategoryᵒᵖ)
    {Z : C} {f g : (∐ F).obj k ⟶ Z}
    (h : ∀ t, (Limits.Sigma.ι F t).app k ≫ f = (Limits.Sigma.ι F t).app k ≫ g) :
    f = g := by
  apply (isColimitOfPreserves ((evaluation _ _).obj k)
    (colimit.isColimit (Discrete.functor F))).hom_ext
  rintro ⟨t⟩
  exact h t

private theorem ι_comp (H : ∀ t, Homotopy (a t) (b t)) {n : ℕ}
    (i : Fin (n + 1)) (t : T) :
    (Limits.Sigma.ι X t).app (op ⦋n⦌) ≫ sigmaMapComponent H i =
      (H t).h i ≫ (Limits.Sigma.ι Y t).app (op ⦋n + 1⦌) := by
  rw [sigmaMapComponent, ← Category.assoc, ι_sigmaIso_hom,
    Limits.Sigma.ι_map_assoc, ι_sigmaIso_inv]

private theorem ι_comp_δ (H : ∀ t, Homotopy (a t) (b t)) {n : ℕ}
    (i : Fin (n + 1)) (j : Fin (n + 2)) (t : T) :
    (Limits.Sigma.ι X t).app (op ⦋n⦌) ≫ (sigmaMapComponent H i ≫ (∐ Y).δ j) =
      ((H t).h i ≫ (Y t).δ j) ≫ (Limits.Sigma.ι Y t).app (op ⦋n⦌) := by
  rw [← Category.assoc, ι_comp, Category.assoc, ← δ_naturality, ← Category.assoc]

private theorem ι_comp_σ (H : ∀ t, Homotopy (a t) (b t)) {n : ℕ}
    (i : Fin (n + 1)) (j : Fin (n + 2)) (t : T) :
    (Limits.Sigma.ι X t).app (op ⦋n⦌) ≫ (sigmaMapComponent H i ≫ (∐ Y).σ j) =
      ((H t).h i ≫ (Y t).σ j) ≫ (Limits.Sigma.ι Y t).app (op ⦋n + 2⦌) := by
  rw [← Category.assoc, ι_comp, Category.assoc, ← σ_naturality, ← Category.assoc]

/-- The coproduct component has the required zero endpoint. -/
@[stacks 08Q4 "coproduct homotopy zero endpoint"]
theorem zero (H : ∀ t, Homotopy (a t) (b t)) (n : ℕ) :
    sigmaMapComponent H (0 : Fin (n + 1)) ≫ (∐ Y).δ 0 =
      (Limits.Sigma.map b).app (op ⦋n⦌) := by
  apply app_hom_ext X (op ⦋n⦌)
  intro t
  rw [ι_comp_δ, (H t).h_zero_comp_δ_zero]
  exact (NatTrans.congr_app (Limits.Sigma.ι_map b t) (op ⦋n⦌)).symm

/-- The coproduct component has the required last endpoint. -/
@[stacks 08Q4 "coproduct homotopy last endpoint"]
theorem last (H : ∀ t, Homotopy (a t) (b t)) (n : ℕ) :
    sigmaMapComponent H (Fin.last n) ≫ (∐ Y).δ (Fin.last (n + 1)) =
      (Limits.Sigma.map a).app (op ⦋n⦌) := by
  apply app_hom_ext X (op ⦋n⦌)
  intro t
  rw [ι_comp_δ, (H t).h_last_comp_δ_last]
  exact (NatTrans.congr_app (Limits.Sigma.ι_map a t) (op ⦋n⦌)).symm

/-- Coproduct components satisfy the first face relation. -/
@[stacks 08Q4 "coproduct homotopy first face relation"]
theorem face_of_le (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    sigmaMapComponent H j.succ ≫ (∐ Y).δ i.castSucc =
      (∐ X).δ i ≫ sigmaMapComponent H j := by
  apply app_hom_ext X (op ⦋n + 1⦌)
  intro t
  rw [ι_comp_δ, (H t).h_succ_comp_δ_castSucc_of_lt i j hij,
    Category.assoc, ← δ_naturality_assoc, ι_comp]

/-- Coproduct components satisfy the adjacent-face relation. -/
@[stacks 08Q4 "coproduct homotopy adjacent face relation"]
theorem face_adjacent (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (j : Fin (n + 1)) :
    sigmaMapComponent H j.succ ≫ (∐ Y).δ j.castSucc.succ =
      sigmaMapComponent H j.castSucc ≫ (∐ Y).δ j.castSucc.succ := by
  apply app_hom_ext X (op ⦋n + 1⦌)
  intro t
  rw [ι_comp_δ, ι_comp_δ, (H t).h_succ_comp_δ_castSucc_succ j]

/-- Coproduct components satisfy the complementary face relation. -/
@[stacks 08Q4 "coproduct homotopy complementary face relation"]
theorem face_of_lt (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    sigmaMapComponent H j.castSucc ≫ (∐ Y).δ i.succ =
      (∐ X).δ i ≫ sigmaMapComponent H j := by
  apply app_hom_ext X (op ⦋n + 1⦌)
  intro t
  rw [ι_comp_δ, (H t).h_castSucc_comp_δ_succ_of_lt i j hji,
    Category.assoc, ← δ_naturality_assoc, ι_comp]

/-- Coproduct components satisfy the first degeneracy relation. -/
@[stacks 08Q4 "coproduct homotopy first degeneracy relation"]
theorem degeneracy_of_le (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    sigmaMapComponent H j ≫ (∐ Y).σ i.castSucc =
      (∐ X).σ i ≫ sigmaMapComponent H j.succ := by
  apply app_hom_ext X (op ⦋n⦌)
  intro t
  rw [ι_comp_σ, (H t).h_comp_σ_castSucc_of_le i j hij,
    Category.assoc, ← σ_naturality_assoc, ι_comp]

/-- Coproduct components satisfy the complementary degeneracy relation. -/
@[stacks 08Q4 "coproduct homotopy complementary degeneracy relation"]
theorem degeneracy_of_lt (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    sigmaMapComponent H j ≫ (∐ Y).σ i.succ =
      (∐ X).σ i ≫ sigmaMapComponent H j.castSucc := by
  apply app_hom_ext X (op ⦋n⦌)
  intro t
  rw [ι_comp_σ, (H t).h_comp_σ_succ_of_lt i j hji,
    Category.assoc, ← σ_naturality_assoc, ι_comp]

end sigmaMapComponent

/-- A family of directed simplicial homotopies induces a directed homotopy between the
coproduct maps. -/
@[stacks 08Q4 "coproducts of simplicial homotopies"]
def sigmaMap (H : ∀ t, Homotopy (a t) (b t)) :
    Homotopy (Limits.Sigma.map a) (Limits.Sigma.map b) where
  h := sigmaMapComponent H
  h_zero_comp_δ_zero := sigmaMapComponent.zero H
  h_last_comp_δ_last := sigmaMapComponent.last H
  h_succ_comp_δ_castSucc_of_lt := sigmaMapComponent.face_of_le H
  h_succ_comp_δ_castSucc_succ := sigmaMapComponent.face_adjacent H
  h_castSucc_comp_δ_succ_of_lt := sigmaMapComponent.face_of_lt H
  h_comp_σ_castSucc_of_le := sigmaMapComponent.degeneracy_of_le H
  h_comp_σ_succ_of_lt := sigmaMapComponent.degeneracy_of_lt H

namespace sigmaMap

/-- The homotopy components of `sigmaMap H` are the canonical pointwise coproduct components. -/
@[simp, stacks 08Q4 "coproduct homotopy component formula"]
theorem h (H : ∀ t, Homotopy (a t) (b t)) {n : ℕ} (i : Fin (n + 1)) :
    (sigmaMap H).h i = sigmaMapComponent H i := rfl

end sigmaMap

end Homotopy

namespace DirectedHomotopy

variable {X Y : T → SimplicialObject C}
variable [FunctorCategory.HasPointwiseCoproduct X]
variable [FunctorCategory.HasPointwiseCoproduct Y]
variable {a b : ∀ t, X t ⟶ Y t}

/-- Coproducts preserve a family of directed simplicial-homotopy relations. Unlike the zigzag
closure, this statement does not require the index type to be finite. -/
@[stacks 08Q4 "coproducts preserve directed simplicial homotopy"]
theorem sigmaMap (hab : ∀ t, DirectedHomotopy (a t) (b t)) :
    DirectedHomotopy (Limits.Sigma.map a) (Limits.Sigma.map b) := by
  exact ⟨Homotopy.sigmaMap (fun t ↦ Classical.choice (hab t))⟩

end DirectedHomotopy

namespace Homotopic

variable [Finite T]
variable {X Y : T → SimplicialObject C}
variable [FunctorCategory.HasPointwiseCoproduct X]
variable [FunctorCategory.HasPointwiseCoproduct Y]
variable {a b : ∀ t, X t ⟶ Y t}

/-- A finite family of zigzag simplicial homotopies induces a zigzag homotopy between the
coproduct maps. -/
@[stacks 08Q4 "finite coproducts preserve simplicial homotopy"]
theorem sigmaMap (hab : ∀ t, Homotopic (a t) (b t)) :
    Homotopic (Limits.Sigma.map a) (Limits.Sigma.map b) := by
  classical
  letI := Fintype.ofFinite T
  have hupdate (f : ∀ t, X t ⟶ Y t) (t : T) {p q : X t ⟶ Y t}
      (hpq : Homotopic p q) :
      Homotopic (Limits.Sigma.map (Function.update f t p))
        (Limits.Sigma.map (Function.update f t q)) := by
    induction hpq with
    | rel p q hpq =>
        apply Relation.EqvGen.rel
        apply DirectedHomotopy.sigmaMap
        intro s
        by_cases hst : s = t
        · subst s
          simpa only [Function.update_self] using hpq
        · simpa only [Function.update_of_ne hst] using
            (show DirectedHomotopy (f s) (f s) from ⟨Homotopy.refl (f s)⟩)
    | refl p => exact Relation.EqvGen.refl _
    | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans p q r _ _ hpq hqr => exact Relation.EqvGen.trans _ _ _ hpq hqr
  have hfin (s : Finset T) :
      Homotopic (Limits.Sigma.map a)
        (Limits.Sigma.map (fun t ↦ if t ∈ s then b t else a t)) := by
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Homotopic, Finset.notMem_empty, ↓reduceIte] using
          Relation.EqvGen.refl (r := DirectedHomotopy) (Limits.Sigma.map a)
    | @insert t s hts ih =>
        let f : ∀ t, X t ⟶ Y t := fun t ↦ if t ∈ s then b t else a t
        have hfa : Function.update f t (a t) = f := by
          apply Function.update_eq_self_iff.mpr
          exact (if_neg hts).symm
        have hfb : Function.update f t (b t) =
            (fun k ↦ if k ∈ insert t s then b k else a k) := by
          funext k
          by_cases hkt : k = t
          · subst k
            simp only [Function.update_self, Finset.mem_insert_self, ↓reduceIte]
          · simp only [Function.update_of_ne hkt, Finset.mem_insert, hkt, false_or, f]
        exact Relation.EqvGen.trans _ _ _ ih
          (by simpa only [Homotopic, hfa, hfb] using hupdate f t (hab t))
  simpa only [Finset.mem_univ, ↓reduceIte] using hfin Finset.univ

end Homotopic

end CategoryTheory.SimplicialObject
