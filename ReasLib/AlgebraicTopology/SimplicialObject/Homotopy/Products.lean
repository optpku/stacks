module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy
public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Product
public import Mathlib.Tactic.CrossRefAttribute

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

/-- The product component has the required zero endpoint. -/
@[stacks 08Q4 "product homotopy zero endpoint"]
theorem zero (H : ∀ t, Homotopy (a t) (b t)) (n : ℕ) :
    piMapComponent H (0 : Fin (n + 1)) ≫ (∏ᶜ Y).δ 0 =
      (Limits.Pi.map b).app (op ⦋n⦌) := sorry

/-- The product component has the required last endpoint. -/
@[stacks 08Q4 "product homotopy last endpoint"]
theorem last (H : ∀ t, Homotopy (a t) (b t)) (n : ℕ) :
    piMapComponent H (Fin.last n) ≫ (∏ᶜ Y).δ (Fin.last (n + 1)) =
      (Limits.Pi.map a).app (op ⦋n⦌) := sorry

/-- Product components satisfy the first face relation. -/
@[stacks 08Q4 "product homotopy first face relation"]
theorem face_of_le (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    piMapComponent H j.succ ≫ (∏ᶜ Y).δ i.castSucc =
      (∏ᶜ X).δ i ≫ piMapComponent H j := sorry

/-- Product components satisfy the adjacent-face relation. -/
@[stacks 08Q4 "product homotopy adjacent face relation"]
theorem face_adjacent (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (j : Fin (n + 1)) :
    piMapComponent H j.succ ≫ (∏ᶜ Y).δ j.castSucc.succ =
      piMapComponent H j.castSucc ≫ (∏ᶜ Y).δ j.castSucc.succ := sorry

/-- Product components satisfy the complementary face relation. -/
@[stacks 08Q4 "product homotopy complementary face relation"]
theorem face_of_lt (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    piMapComponent H j.castSucc ≫ (∏ᶜ Y).δ i.succ =
      (∏ᶜ X).δ i ≫ piMapComponent H j := sorry

/-- Product components satisfy the first degeneracy relation. -/
@[stacks 08Q4 "product homotopy first degeneracy relation"]
theorem degeneracy_of_le (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    piMapComponent H j ≫ (∏ᶜ Y).σ i.castSucc =
      (∏ᶜ X).σ i ≫ piMapComponent H j.succ := sorry

/-- Product components satisfy the complementary degeneracy relation. -/
@[stacks 08Q4 "product homotopy complementary degeneracy relation"]
theorem degeneracy_of_lt (H : ∀ t, Homotopy (a t) (b t))
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    piMapComponent H j ≫ (∏ᶜ Y).σ i.succ =
      (∏ᶜ X).σ i ≫ piMapComponent H j.castSucc := sorry

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
    (piMap H).h i = piMapComponent H i := sorry

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
    DirectedHomotopy (Limits.Pi.map a) (Limits.Pi.map b) := sorry

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
    Homotopic (Limits.Pi.map a) (Limits.Pi.map b) := sorry

end Homotopic

end CategoryTheory.SimplicialObject
