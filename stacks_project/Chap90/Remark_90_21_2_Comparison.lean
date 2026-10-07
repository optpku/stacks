module

public import Mathlib.CategoryTheory.Functor.Category
public import stacks_project.Chap90.Definition_90_21_1_Groupoid

/-!
# Morphisms of groupoids in functors as natural transformations

A morphism of groupoids in functors on `C` corresponds to a morphism of the
associated functors `C ⥤ Grpd`, where `Grpd` is regarded as a 1-category.
This comparison is at the level of `Hom` types, not an identification of
`GroupoidInFunctors` with `C ⥤ Grpd` or with the associated cofibered category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

namespace Hom

/-- The natural transformation of `C ⥤ Grpd` induced by a morphism of groupoids in functors. -/
def toNatTrans {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    G.toFunctor ⟶ H.toFunctor where
  app T := f.mapPoints T
  naturality := sorry

/-- The component of `toNatTrans f` at `T` is the fibrewise functor `f.mapPoints T`. -/
theorem toNatTrans_app {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) (T : C) :
    (toNatTrans f).app T = f.mapPoints T := sorry

/-- The morphism of groupoids in functors induced by a natural transformation of `toFunctor`. -/
def ofNatTrans {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) : Hom G H where
  obj :=
    { app T := TypeCat.ofHom fun x ↦ (α.app T).obj x
      naturality := sorry }
  arrow :=
    { app T := TypeCat.ofHom fun a ↦ ((α.app T).map (PointHom.ofArrow a rfl rfl)).arrow
      naturality := sorry }
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of `ofNatTrans α` at `T` is the object map of `α.app T`. -/
theorem ofNatTrans_obj {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) (T : C) (x : G.U.obj T) :
    (ofNatTrans α).obj.app T x = (α.app T).obj x := sorry

/-- The arrow component of `ofNatTrans α` at `T` is the image arrow under `α.app T`. -/
theorem ofNatTrans_arrow {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) (T : C) (a : G.R.obj T) :
    (ofNatTrans α).arrow.app T a =
      ((α.app T).map (PointHom.ofArrow a rfl rfl)).arrow := sorry

/-- Morphisms of groupoids in functors correspond to morphisms of the associated
functors `C ⥤ Grpd`. -/
def equivToNatTrans (G H : GroupoidInFunctors.{u, v, w} C) :
    Hom G H ≃ (G.toFunctor ⟶ H.toFunctor) where
  toFun := toNatTrans
  invFun := ofNatTrans
  left_inv := sorry
  right_inv := sorry

/-- `equivToNatTrans` sends a morphism to the associated natural transformation. -/
theorem equivToNatTrans_apply {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    equivToNatTrans G H f = toNatTrans f := sorry

/-- The inverse of `equivToNatTrans` sends a natural transformation to `ofNatTrans`. -/
theorem equivToNatTrans_symm_apply {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) :
    (equivToNatTrans G H).symm α = ofNatTrans α := sorry

end Hom

end CategoryTheory.GroupoidInFunctors
