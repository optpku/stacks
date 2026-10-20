module

public import ReasLib.CategoryTheory.Fibered.Inertia.Based.Construction
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of maps of inertia over a base

This file owns the `1`-morphism action of relative and absolute inertia for based categories
over a fixed base. It deliberately assumes no fibredness: cartesian properties and
projection-level computations belong to later leaves.
-/

@[expose] public section

universe u v u₁ v₁ u₁' v₁' u₂ v₂ u₂' v₂' u₃ v₃

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

section Map

variable
    {S₁ : BasedCategory.{v₁, u₁} C} {S₁' : BasedCategory.{v₁', u₁'} C}
    {S₂ : BasedCategory.{v₂, u₂} C} {S₂' : BasedCategory.{v₂', u₂'} C}

/-- The relative-inertia map induced by an invertibly commuting based square lies over the
common base. -/
@[stacks 04Z4 "relative-inertia square map projection computation"]
theorem RelativeInertia.map.comm
    {F₁ : S₁ ⥤ᵇ S₁'} {F₂ : S₂ ⥤ᵇ S₂'}
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂) :
    CategoryTheory.RelativeInertia.map G.toFunctor G'.toFunctor
          (BasedNatIso.toNatIso comm) ⋙
        (relativeInertia F₂).p =
      (relativeInertia F₁).p := sorry
/- Proof strategy: use functor extensionality. On objects the equation is `G.w_obj`; on
morphisms it follows from `G.w` and `RelativeInertia.map.hom`. -/

/-- An invertibly commuting square in `Cat/C` induces a map on based relative inertia. -/
@[stacks 04Z4 "(1) relative-inertia square map"]
def RelativeInertia.map
    {F₁ : S₁ ⥤ᵇ S₁'} {F₂ : S₂ ⥤ᵇ S₂'}
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂) :
    relativeInertia F₁ ⥤ᵇ relativeInertia F₂ where
  toFunctor := CategoryTheory.RelativeInertia.map G.toFunctor G'.toFunctor
    (BasedNatIso.toNatIso comm)
  w := RelativeInertia.map.comm G G' comm

namespace Inertia.map

/-- The canonical invertible comparison for the square defining the map on absolute inertia.
It is assembled from the functor right unitor and the strict projection comparison of `G`. -/
@[stacks 04Z4 "absolute-inertia map square isomorphism"]
def squareIso (G : S₁ ⥤ᵇ S₂) :
    S₁.p ⋙ 𝟭 C ≅ G.toFunctor ⋙ S₂.p :=
  Functor.rightUnitor S₁.p ≪≫ G.projectionIso.symm

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The induced map on absolute inertia lies over the base. -/
private theorem comm (G : S₁ ⥤ᵇ S₂) :
    CategoryTheory.RelativeInertia.map G.toFunctor (𝟭 C) (squareIso G) ⋙
        (inertia S₂).p =
      (inertia S₁).p := sorry

end Inertia.map

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A based functor induces a map on based absolute inertia. -/
@[stacks 04Z4 "(2) absolute-inertia map"]
def Inertia.map (G : S₁ ⥤ᵇ S₂) :
    inertia S₁ ⥤ᵇ inertia S₂ where
  toFunctor := CategoryTheory.RelativeInertia.map G.toFunctor (𝟭 C)
    (Inertia.map.squareIso G)
  w := Inertia.map.comm G

end Map

end BasedCategory
end CategoryTheory
