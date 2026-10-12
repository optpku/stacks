/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of full-subcategory restriction

A categorical family of ambient functors that all carry `P` into `Q` induces
a categorical family of restricted functors.  This packages the identity and
composition laws once for all downstream specializations.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.ObjectProperty.FullSubcategory.restrict

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {S : Type u₃} [Category.{v₃} S]
variable {P : ObjectProperty C} {Q : ObjectProperty D}

/-- Identity law for the restricted action of a categorical family of
ambient functors. -/
theorem functor_map_id (Φ : S ⥤ (C ⥤ D))
    (hΦ : ∀ s, P ≤ Q.inverseImage (Φ.obj s)) (s : S) :
    natTrans (hΦ s) (hΦ s) (Φ.map (𝟙 s)) =
      𝟙 (restrict (Φ.obj s) (hΦ s)) := sorry

/-- Composition law for the restricted action of a categorical family of
ambient functors. -/
theorem functor_map_comp (Φ : S ⥤ (C ⥤ D))
    (hΦ : ∀ s, P ≤ Q.inverseImage (Φ.obj s))
    {r s t : S} (f : r ⟶ s) (g : s ⟶ t) :
    natTrans (hΦ r) (hΦ t) (Φ.map (f ≫ g)) =
      natTrans (hΦ r) (hΦ s) (Φ.map f) ≫
        natTrans (hΦ s) (hΦ t) (Φ.map g) := sorry

/-- Restriction acts functorially on any categorical family of ambient
functors whose objects carry `P` into `Q`. -/
@[stacks 001D "functorial restriction to full subcategories"]
def functor (Φ : S ⥤ (C ⥤ D))
    (hΦ : ∀ s, P ≤ Q.inverseImage (Φ.obj s)) :
    S ⥤ (P.FullSubcategory ⥤ Q.FullSubcategory) where
  obj s := restrict (Φ.obj s) (hΦ s)
  map f := natTrans (hΦ _) (hΦ _) (Φ.map f)
  map_id s := functor_map_id Φ hΦ s
  map_comp f g := functor_map_comp Φ hΦ f g

/-- The restricted family acts on objects by restricting the corresponding
ambient functor. -/
@[simp]
theorem functor_obj (Φ : S ⥤ (C ⥤ D))
    (hΦ : ∀ s, P ≤ Q.inverseImage (Φ.obj s)) (s : S) :
    (functor Φ hΦ).obj s = restrict (Φ.obj s) (hΦ s) := sorry

/-- The restricted family acts on morphisms by restricting the corresponding
ambient natural transformation. -/
@[simp]
theorem functor_map (Φ : S ⥤ (C ⥤ D))
    (hΦ : ∀ s, P ≤ Q.inverseImage (Φ.obj s))
    {s t : S} (f : s ⟶ t) :
    (functor Φ hΦ).map f = natTrans (hΦ s) (hΦ t) (Φ.map f) := sorry

end CategoryTheory.ObjectProperty.FullSubcategory.restrict
