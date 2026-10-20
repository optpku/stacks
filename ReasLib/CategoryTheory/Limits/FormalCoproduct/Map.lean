/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Basic

/-!
# Functoriality of formal coproducts

This module makes the category of formal coproducts functorial in its ambient category.  The
construction retains the indexing type and applies a functor to every component.
-/

@[expose] public section

universe w v u v' u' v'' u''

namespace CategoryTheory
namespace Limits
namespace FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- The object action underlying componentwise mapping of formal coproducts. -/
def mapObj {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (K : FormalCoproduct.{w} C) : FormalCoproduct.{w} D :=
  ⟨K.I, fun i ↦ F.obj (K.obj i)⟩

/-- The morphism action underlying componentwise mapping of formal coproducts. -/
def mapHom {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    {K L : FormalCoproduct.{w} C} (phi : K ⟶ L) :
    mapObj F K ⟶ mapObj F L :=
  ⟨phi.f, fun i ↦ F.map (phi.φ i)⟩

/-- The componentwise morphism action preserves identities. -/
theorem mapHom_id {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (K : FormalCoproduct.{w} C) :
    mapHom F (𝟙 K) = 𝟙 (mapObj F K) := sorry

/-- The componentwise morphism action preserves composition. -/
theorem mapHom_comp {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    {K L M : FormalCoproduct.{w} C} (phi : K ⟶ L) (psi : L ⟶ M) :
    mapHom F (phi ≫ psi) = mapHom F phi ≫ mapHom F psi := sorry

/-- Applying a functor componentwise to a formal coproduct. -/
def map {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    FormalCoproduct.{w} C ⥤ FormalCoproduct.{w} D where
  obj := mapObj F
  map := mapHom F
  map_id := mapHom_id F
  map_comp := mapHom_comp F

/-- Componentwise mapping along the identity functor is the identity on formal coproducts. -/
theorem map_id :
    map (𝟭 C) = 𝟭 (FormalCoproduct.{w} C) := sorry

/-- Componentwise mapping commutes with composition of ambient functors. -/
theorem map_comp {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    map (F ⋙ G) = map F ⋙ map G := sorry

/-- Componentwise mapping of a formal coproduct retains its indexing type. -/
@[simp]
theorem map_obj_index {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (K : FormalCoproduct.{w} C) :
    ((map F).obj K).I = K.I := sorry

/-- Componentwise mapping applies the functor to each object of a formal coproduct. -/
@[simp]
theorem map_obj_obj {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (K : FormalCoproduct.{w} C) (i : K.I) :
    ((map F).obj K).obj i = F.obj (K.obj i) := sorry

/-- The index function of a componentwise-mapped formal-coproduct morphism is unchanged. -/
@[simp]
theorem map_map_f {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    {K L : FormalCoproduct.{w} C} (φ : K ⟶ L) :
    ((map F).map φ).f = φ.f := sorry

/-- The components of a mapped formal-coproduct morphism are the functorial images of its
original components. -/
@[simp]
theorem map_map_φ {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    {K L : FormalCoproduct.{w} C} (φ : K ⟶ L) (i : K.I) :
    ((map F).map φ).φ i = F.map (φ.φ i) := sorry

end FormalCoproduct
end Limits
end CategoryTheory
