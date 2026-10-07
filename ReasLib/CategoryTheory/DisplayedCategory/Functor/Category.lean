module

public import ReasLib.CategoryTheory.DisplayedCategory.NatTrans

/-!
# Category of displayed functors over a fixed base functor

For fixed `F : C ⥤ C'`, displayed functors over `F` form a category whose morphisms are displayed
natural transformations over `𝟙 F`.  This packages the normalized identity and vertical
composition API so ordinary category notation, isomorphisms, and functorial constructions can be
used directly.
-/

@[expose] public section

namespace CategoryTheory

universe v u v' u'

namespace DisplayedFunctor

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
variable {D : DisplayedCategory C} {E : DisplayedCategory C'} {F : C ⥤ C'}

/-- The category of displayed functors over a fixed base functor. -/
instance category : Category (DisplayedFunctor D E F) where
  Hom Φ Ψ := DisplayedNatTrans Φ Ψ (𝟙 F)
  id Φ := DisplayedNatTrans.id Φ
  comp η θ := DisplayedNatTrans.vcomp η θ
  id_comp := DisplayedNatTrans.id_vcomp
  comp_id := DisplayedNatTrans.vcomp_id
  assoc := DisplayedNatTrans.vcomp_assoc

/-- The component of a categorical identity between displayed functors is the displayed
identity. -/
@[simp]
theorem category_id_app (Φ : DisplayedFunctor D E F) {X : C} (x : D.obj X) :
    (𝟙 Φ : Φ ⟶ Φ).app x = E.id (Φ.obj x) := sorry

/-- Categorical composition between displayed functors is normalized displayed vertical
composition. -/
@[simp]
theorem category_comp_app
    {Φ Ψ Χ : DisplayedFunctor D E F} (η : Φ ⟶ Ψ) (θ : Ψ ⟶ Χ)
    {X : C} (x : D.obj X) :
    (η ≫ θ).app x =
      DisplayedCategory.Hom.cast E (Category.comp_id (𝟙 (F.obj X)))
        (E.comp (η.app x) (θ.app x)) := sorry

/-- Totalization is functorial on the category of displayed functors over `F`. -/
def totalFunctor (D : DisplayedCategory C) (E : DisplayedCategory C') (F : C ⥤ C') :
    DisplayedFunctor D E F ⥤
      (DisplayedCategory.Total D ⥤ DisplayedCategory.Total E) where
  obj Φ := total Φ
  map η := DisplayedNatTrans.total η
  map_id := DisplayedNatTrans.total_id
  map_comp := DisplayedNatTrans.total_vcomp

/-- `totalFunctor` sends a displayed functor to its totalization. -/
@[simp]
theorem totalFunctor_obj (Φ : DisplayedFunctor D E F) :
    (totalFunctor D E F).obj Φ = total Φ := rfl

/-- `totalFunctor` sends a displayed transformation to its totalization. -/
@[simp]
theorem totalFunctor_map {Φ Ψ : DisplayedFunctor D E F} (η : Φ ⟶ Ψ) :
    (totalFunctor D E F).map η = DisplayedNatTrans.total η := rfl

end DisplayedFunctor

end CategoryTheory
