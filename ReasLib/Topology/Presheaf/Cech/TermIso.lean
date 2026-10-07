module

public import ReasLib.Topology.Presheaf.Cech.Coordinates
public import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coordinate comparison for ordinary Čech complexes

The ordinary Čech degree objects are compared with tuple-indexed section groups, and their
differentials are identified with the alternating coordinate formula.
-/

@[expose] public section

open CategoryTheory Opposite TopCat.Presheaf TopologicalSpace
open CategoryTheory.Limits
open scoped BigOperators

noncomputable section

universe u v

namespace TopCat.Presheaf.Cech

variable {X : TopCat.{u}} {ι : Type v}

/- The ordinary Cech owner and the coordinate product use definitionally different presentations.
   This file records the concrete comparison once, so later ordered/alternating constructions do
   not need to rebuild the product data. -/

/-- The degree object of the ordinary Čech complex is the product of its coordinate section
groups. -/
@[stacks 01EF "ordinary Cech degree/product comparison"]
theorem complex_obj_X_eq_product (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (TopCat.Presheaf.cechComplex 𝒰 F).X p =
      ∏ᶜ fun σ : Fin (p + 1) → ι ↦ F.obj (op (intersection 𝒰 σ)) := sorry

/-- Evaluation at one tuple is the canonical projection from the coordinate term. -/
def termEval (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (σ : Fin (p + 1) → ι) :
    term 𝒰 F p ⟶ F.obj (op (intersection 𝒰 σ)) :=
  AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
    (fun τ : Fin (p + 1) → ι ↦ F.obj (op (intersection 𝒰 τ))) σ)

/-- The coordinatewise projection map into the function presentation. -/
def termProductHom (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (∏ᶜ fun σ : Fin (p + 1) → ι ↦ F.obj (op (intersection 𝒰 σ))) ⟶ term 𝒰 F p :=
  AddCommGrpCat.ofHom (AddMonoidHom.pi
    (fun σ : Fin (p + 1) → ι ↦
      AddCommGrpCat.Hom.hom (Pi.π
        (fun τ : Fin (p + 1) → ι ↦ F.obj (op (intersection 𝒰 τ))) σ)))

/-- The map assembling a tuple-indexed family of sections into a product. -/
def termProductInv (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    term 𝒰 F p ⟶ (∏ᶜ fun σ : Fin (p + 1) → ι ↦ F.obj (op (intersection 𝒰 σ))) :=
  Pi.lift (fun σ : Fin (p + 1) → ι ↦ termEval 𝒰 F p σ)

/-- The projection and assembly maps are inverse in the product presentation. -/
theorem termProductHom_inv_id (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    termProductHom 𝒰 F p ≫ termProductInv 𝒰 F p = 𝟙 _ := sorry

/-- The assembly and projection maps are inverse on tuple-indexed functions. -/
theorem termProductInv_hom_id (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    termProductInv 𝒰 F p ≫ termProductHom 𝒰 F p = 𝟙 _ := sorry

/-- The canonical product/function comparison for the ordinary Čech degree. -/
noncomputable def termProductIso (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (∏ᶜ fun σ : Fin (p + 1) → ι ↦ F.obj (op (intersection 𝒰 σ))) ≅ term 𝒰 F p where
  hom := termProductHom 𝒰 F p
  inv := termProductInv 𝒰 F p
  hom_inv_id := termProductHom_inv_id 𝒰 F p
  inv_hom_id := termProductInv_hom_id 𝒰 F p

/-- The ordinary Čech degree object compared with the explicit coordinate term. -/
noncomputable def termIso (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (TopCat.Presheaf.cechComplex 𝒰 F).X p ≅ term 𝒰 F p :=
  eqToIso (complex_obj_X_eq_product 𝒰 F p) ≪≫ termProductIso 𝒰 F p

/-- The coordinate comparison intertwines the ordinary Čech differential and its
alternating-sum formula. -/
@[stacks 01EE "ordinary Cech differential in coordinates"]
theorem termIso_comm_d (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (TopCat.Presheaf.cechComplex 𝒰 F).d p (p + 1) ≫ (termIso 𝒰 F (p + 1)).hom =
      (termIso 𝒰 F p).hom ≫ differential 𝒰 F p := sorry

/-- Evaluating `termIso_comm_d` at a cochain and tuple gives the coordinate differential formula. -/
@[simp]
theorem termIso_hom_d_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (TopCat.Presheaf.cechComplex 𝒰 F).X p) (σ : Fin (p + 2) → ι) :
    (termIso 𝒰 F (p + 1)).hom ((TopCat.Presheaf.cechComplex 𝒰 F).d p (p + 1) s) σ =
      differentialToFun 𝒰 F p ((termIso 𝒰 F p).hom s) σ := sorry

end TopCat.Presheaf.Cech

end
