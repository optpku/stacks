/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Binary biproducts and products in `ModuleCat`

Mathlib owns the explicit product model `ModuleCat.biprodIsoProd` and its
inverse projection formulas.  This leaf supplies the complementary forward
comparison and naturality formulas used by matrix and short-complex
consumers.  The statements are independent of any chapter presentation.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

variable {R : Type u} [Ring R]

/-- The forward product comparison identifies the first biproduct projection. -/
@[stacks 0192 "ModuleCat biproduct/product first projection"]
theorem biprodIsoProd_hom_comp_fst (M N : ModuleCat.{v} R) :
    (biprodIsoProd M N).hom ≫ ofHom (LinearMap.fst R M N) = biprod.fst := by
  rw [← cancel_epi (biprodIsoProd M N).inv]
  simp

/-- The forward product comparison identifies the second biproduct projection. -/
@[stacks 0192 "ModuleCat biproduct/product second projection"]
theorem biprodIsoProd_hom_comp_snd (M N : ModuleCat.{v} R) :
    (biprodIsoProd M N).hom ≫ ofHom (LinearMap.snd R M N) = biprod.snd := by
  rw [← cancel_epi (biprodIsoProd M N).inv]
  simp

/-- The left biproduct inclusion becomes the ordinary product inclusion. -/
@[stacks 0192 "ModuleCat biproduct/product left inclusion"]
theorem biprodIsoProd_inl_hom (M N : ModuleCat.{v} R) :
    biprod.inl ≫ (biprodIsoProd M N).hom = ofHom (LinearMap.inl R M N) := by
  rw [← cancel_mono (biprodIsoProd M N).inv, biprod.ext_to_iff]
  constructor <;> simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    biprod.inl_fst, biprod.inl_snd, biprodIsoProd_inv_comp_fst,
    biprodIsoProd_inv_comp_snd]
  all_goals apply ModuleCat.hom_ext <;> rfl

/-- The right biproduct inclusion becomes the ordinary product inclusion. -/
@[stacks 0192 "ModuleCat biproduct/product right inclusion"]
theorem biprodIsoProd_inr_hom (M N : ModuleCat.{v} R) :
    biprod.inr ≫ (biprodIsoProd M N).hom = ofHom (LinearMap.inr R M N) := by
  rw [← cancel_mono (biprodIsoProd M N).inv, biprod.ext_to_iff]
  constructor <;> simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    biprod.inr_fst, biprod.inr_snd, biprodIsoProd_inv_comp_fst,
    biprodIsoProd_inv_comp_snd]
  all_goals apply ModuleCat.hom_ext <;> rfl

/-- The forward product comparison sends a left summand element to `(x, 0)`. -/
@[stacks 0192 "ModuleCat biproduct/product left element"]
theorem biprodIsoProd_hom_inl_apply (M N : ModuleCat.{v} R) (x : M) :
    ((biprodIsoProd M N).hom.hom) ((biprod.inl : M ⟶ biprod M N).hom x) = (x, 0) := by
  exact ConcreteCategory.congr_hom (biprodIsoProd_inl_hom M N) x

/-- The forward product comparison sends a right summand element to `(0, y)`. -/
@[stacks 0192 "ModuleCat biproduct/product right element"]
theorem biprodIsoProd_hom_inr_apply (M N : ModuleCat.{v} R) (y : N) :
    ((biprodIsoProd M N).hom.hom) ((biprod.inr : N ⟶ biprod M N).hom y) = (0, y) := by
  exact ConcreteCategory.congr_hom (biprodIsoProd_inr_hom M N) y

/-- The product comparison commutes with maps on both biproduct summands. -/
@[stacks 0192 "ModuleCat biproduct/product map naturality"]
theorem biprod_map_comp_biprodIsoProd_hom
    {M₁ M₂ N₁ N₂ : ModuleCat.{v} R} (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂) :
    biprod.map f g ≫ (biprodIsoProd N₁ N₂).hom =
      (biprodIsoProd M₁ M₂).hom ≫ ofHom (f.hom.prodMap g.hom) := by
  have hfst :
      ofHom (f.hom.prodMap g.hom) ≫ ofHom (LinearMap.fst R N₁ N₂) =
        ofHom (LinearMap.fst R M₁ M₂) ≫ f := by
    apply ModuleCat.hom_ext
    rfl
  have hsnd :
      ofHom (f.hom.prodMap g.hom) ≫ ofHom (LinearMap.snd R N₁ N₂) =
        ofHom (LinearMap.snd R M₁ M₂) ≫ g := by
    apply ModuleCat.hom_ext
    rfl
  rw [← cancel_mono (biprodIsoProd N₁ N₂).inv, biprod.ext_to_iff]
  constructor
  · calc
      _ = biprod.map f g ≫ biprod.fst := by simp
      _ = biprod.fst ≫ f := biprod.map_fst _ _
      _ = (((biprodIsoProd M₁ M₂).hom ≫ ofHom (f.hom.prodMap g.hom)) ≫
          (biprodIsoProd N₁ N₂).inv) ≫ biprod.fst := by
        symm
        rw [Category.assoc, biprodIsoProd_inv_comp_fst, Category.assoc, hfst,
          ← Category.assoc, biprodIsoProd_hom_comp_fst]
  · calc
      _ = biprod.map f g ≫ biprod.snd := by simp
      _ = biprod.snd ≫ g := biprod.map_snd _ _
      _ = (((biprodIsoProd M₁ M₂).hom ≫ ofHom (f.hom.prodMap g.hom)) ≫
          (biprodIsoProd N₁ N₂).inv) ≫ biprod.snd := by
        symm
        rw [Category.assoc, biprodIsoProd_inv_comp_snd, Category.assoc, hsnd,
          ← Category.assoc, biprodIsoProd_hom_comp_snd]

/-- In product coordinates, a biproduct map acts by the product of its two linear maps. -/
@[stacks 0192 "ModuleCat biproduct/product map evaluation"]
theorem biprodIsoProd_map_apply
    {M₁ M₂ N₁ N₂ : ModuleCat.{v} R} (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂)
    (x : M₁ × M₂) :
    ((biprodIsoProd N₁ N₂).hom.hom)
      ((biprod.map f g).hom ((biprodIsoProd M₁ M₂).inv.hom x)) =
        (f.hom.prodMap g.hom) x := by
  have h := ConcreteCategory.congr_hom
    (biprod_map_comp_biprodIsoProd_hom f g) ((biprodIsoProd M₁ M₂).inv.hom x)
  simpa using h

namespace Biprod

/-- A block morphism with zero off-diagonal components and identity lower-right component is the
corresponding diagonal biproduct map. -/
@[stacks 0192 "ModuleCat diagonal biproduct block"]
theorem eq_map_fst_id_of_components
    {X₁ Y₁ Y₂ : ModuleCat.{v} R}
    (F : biprod X₁ Y₂ ⟶ biprod Y₁ Y₂)
    (h_inl_snd : biprod.inl ≫ F ≫ biprod.snd = 0)
    (h_inr_fst : biprod.inr ≫ F ≫ biprod.fst = 0)
    (h_inr_snd : biprod.inr ≫ F ≫ biprod.snd = 𝟙 Y₂) :
    F = biprod.map (biprod.inl ≫ F ≫ biprod.fst) (𝟙 Y₂) := by
  rw [biprod.ext_from_iff]
  constructor
  · rw [biprod.inl_map, biprod.ext_to_iff]
    constructor
    · simp
    · simpa [Category.assoc] using h_inl_snd
  · rw [biprod.inr_map, biprod.ext_to_iff]
    constructor
    · simpa [Category.assoc] using h_inr_fst
    · simpa [Category.assoc] using h_inr_snd

end Biprod

/- The inverse projection formulas are canonical Mathlib declarations. -/

end ModuleCat

end
