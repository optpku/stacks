module

public import ReasLib.CategoryTheory.DisplayedCategory.Functor

/-!
# Computation for displayed functors

These small component lemmas keep identity and composite displayed functors usable without
unfolding their dependent structure.  The canonical data remain owned by `DisplayedFunctor.id`
and `DisplayedFunctor.comp`.
-/

@[expose] public section

namespace CategoryTheory

universe v u v' u' v'' u''

namespace DisplayedFunctor

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
variable {C'' : Type u''} [Category.{v''} C'']
variable {D : DisplayedCategory C} {E : DisplayedCategory C'}
variable {E' : DisplayedCategory C''} {F : C ⥤ C'} {G : C' ⥤ C''}

/-- The object map of the identity displayed functor is the identity. -/
@[simp]
theorem id_obj (D : DisplayedCategory C) {X : C} (x : D.obj X) :
    (id D).obj x = x := sorry

/-- The morphism map of the identity displayed functor is the identity. -/
@[simp]
theorem id_map (D : DisplayedCategory C) {X Y : C} {f : X ⟶ Y}
    {x : D.obj X} {y : D.obj Y} (φ : D.Hom f x y) :
    (id D).map φ = φ := sorry

/-- The object map of a composite displayed functor is the composite object map. -/
@[simp]
theorem comp_obj {H : C' ⥤ C''}
    (Φ : DisplayedFunctor D E F) (Ψ : DisplayedFunctor E E' H)
    {X : C} (x : D.obj X) :
    (comp Φ Ψ).obj x = Ψ.obj (Φ.obj x) := sorry

/-- The morphism map of a composite displayed functor is the composite displayed map. -/
@[simp]
theorem comp_map {H : C' ⥤ C''}
    (Φ : DisplayedFunctor D E F) (Ψ : DisplayedFunctor E E' H)
    {X Y : C} {f : X ⟶ Y} {x : D.obj X} {y : D.obj Y} (φ : D.Hom f x y) :
    (comp Φ Ψ).map φ = Ψ.map (Φ.map φ) := sorry

end DisplayedFunctor

end CategoryTheory
