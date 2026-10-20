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

/-- The coproduct component has the required zero endpoint. -/
@[stacks 08Q4 "coproduct homotopy zero endpoint"]
theorem zero (H : ∀ t, Homotopy (a t) (b t)) (n : ℕ) :
    sigmaMapComponent H (0 : Fin (n + 1)) ≫ (∐ Y).δ 0 =
      (Limits.Sigma.map b).app (op ⦋n⦌) := sorry

/-- The coproduct component has the required last endpoint. -/
@[stacks 08Q4 "coproduct homotopy last endpoint"]
theorem last (H : ∀ t, Homotopy (a t) (b t)) (n : ℕ) :
    sigmaMapComponent H (Fin.last n) ≫ (∐ Y).δ (Fin.last (n + 1)) =
      (Limits.Sigma.map a).app (op ⦋n⦌) := sorry

/-- Coproduct components satisfy the first face relation. -/
@[stacks 08Q4 "coproduct homotopy first face relation"]
theorem face_of_le (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    sigmaMapComponent H j.succ ≫ (∐ Y).δ i.castSucc =
      (∐ X).δ i ≫ sigmaMapComponent H j := sorry

/-- Coproduct components satisfy the adjacent-face relation. -/
@[stacks 08Q4 "coproduct homotopy adjacent face relation"]
theorem face_adjacent (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (j : Fin (n + 1)) :
    sigmaMapComponent H j.succ ≫ (∐ Y).δ j.castSucc.succ =
      sigmaMapComponent H j.castSucc ≫ (∐ Y).δ j.castSucc.succ := sorry

/-- Coproduct components satisfy the complementary face relation. -/
@[stacks 08Q4 "coproduct homotopy complementary face relation"]
theorem face_of_lt (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    sigmaMapComponent H j.castSucc ≫ (∐ Y).δ i.succ =
      (∐ X).δ i ≫ sigmaMapComponent H j := sorry

/-- Coproduct components satisfy the first degeneracy relation. -/
@[stacks 08Q4 "coproduct homotopy first degeneracy relation"]
theorem degeneracy_of_le (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    sigmaMapComponent H j ≫ (∐ Y).σ i.castSucc =
      (∐ X).σ i ≫ sigmaMapComponent H j.succ := sorry

/-- Coproduct components satisfy the complementary degeneracy relation. -/
@[stacks 08Q4 "coproduct homotopy complementary degeneracy relation"]
theorem degeneracy_of_lt (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    sigmaMapComponent H j ≫ (∐ Y).σ i.succ =
      (∐ X).σ i ≫ sigmaMapComponent H j.castSucc := sorry

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
    (sigmaMap H).h i = sigmaMapComponent H i := sorry

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
    DirectedHomotopy (Limits.Sigma.map a) (Limits.Sigma.map b) := sorry

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
    Homotopic (Limits.Sigma.map a) (Limits.Sigma.map b) := sorry

end Homotopic

end CategoryTheory.SimplicialObject
