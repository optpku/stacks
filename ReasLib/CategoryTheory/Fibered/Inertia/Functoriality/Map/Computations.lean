module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for maps of inertia over a base

This leaf exposes the underlying functor, object, automorphism, morphism, and square-comparison
formulas for the relative and absolute based-inertia maps.
-/

@[expose] public section

universe u v u₁ v₁ u₁' v₁' u₂ v₂ u₂' v₂'

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]
variable
    {S₁ : BasedCategory.{v₁, u₁} C} {S₁' : BasedCategory.{v₁', u₁'} C}
    {S₂ : BasedCategory.{v₂, u₂} C} {S₂' : BasedCategory.{v₂', u₂'} C}

/-- The underlying functor of a based relative-inertia map is the neutral map attached to its
invertibly commuting square. -/
@[simp, stacks 04Z4 "relative-inertia map total-functor computation"]
theorem RelativeInertia.map.toFunctor
    {F₁ : S₁ ⥤ᵇ S₁'} {F₂ : S₂ ⥤ᵇ S₂'}
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂) :
    (RelativeInertia.map G G' comm).toFunctor =
      CategoryTheory.RelativeInertia.map G.toFunctor G'.toFunctor
        (BasedNatIso.toNatIso comm) := sorry

/-- A based relative-inertia map applies the source-side based functor to the underlying
object. -/
@[simp, stacks 04Z4 "relative-inertia map object computation"]
theorem RelativeInertia.map.obj
    {F₁ : S₁ ⥤ᵇ S₁'} {F₂ : S₂ ⥤ᵇ S₂'}
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂) (A : (relativeInertia F₁).obj) :
    ((RelativeInertia.map G G' comm).toFunctor.obj A).obj =
      G.toFunctor.obj A.obj := sorry

/-- A based relative-inertia map applies the source-side based functor to the chosen
automorphism. -/
@[simp, stacks 04Z4 "relative-inertia map automorphism computation"]
theorem RelativeInertia.map.aut
    {F₁ : S₁ ⥤ᵇ S₁'} {F₂ : S₂ ⥤ᵇ S₂'}
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂) (A : (relativeInertia F₁).obj) :
    ((RelativeInertia.map G G' comm).toFunctor.obj A).aut =
      G.toFunctor.mapIso A.aut := sorry

/-- A based relative-inertia map applies the source-side based functor to the underlying
arrow. -/
@[simp, stacks 04Z4 "relative-inertia map underlying-arrow computation"]
theorem RelativeInertia.map.hom
    {F₁ : S₁ ⥤ᵇ S₁'} {F₂ : S₂ ⥤ᵇ S₂'}
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)
    {A B : (relativeInertia F₁).obj} (φ : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom
        ((RelativeInertia.map G G' comm).toFunctor.map φ) =
      G.toFunctor.map (CategoryTheory.RelativeInertia.hom φ) := sorry

namespace Inertia.map.squareIso

/-- The forward component of the square comparison is the right unitor followed by the
inverse strict projection comparison. -/
@[simp, stacks 04Z4 "absolute-inertia square comparison forward component"]
theorem hom.app (G : S₁ ⥤ᵇ S₂) (x : S₁.obj) :
    (Inertia.map.squareIso G).hom.app x =
      (Functor.rightUnitor S₁.p).hom.app x ≫ G.projectionIso.inv.app x := sorry

/-- The inverse component of the square comparison is the strict projection comparison
followed by the inverse right unitor. -/
@[simp, stacks 04Z4 "absolute-inertia square comparison inverse component"]
theorem inv.app (G : S₁ ⥤ᵇ S₂) (x : S₁.obj) :
    (Inertia.map.squareIso G).inv.app x =
      G.projectionIso.hom.app x ≫ (Functor.rightUnitor S₁.p).inv.app x := sorry

end Inertia.map.squareIso

namespace Inertia.map

/-- The underlying functor of the map on based absolute inertia is the corresponding neutral
relative-inertia map. -/
@[simp, stacks 04Z4 "absolute-inertia map total-functor computation"]
theorem toFunctor (G : S₁ ⥤ᵇ S₂) :
    (Inertia.map G).toFunctor =
      CategoryTheory.RelativeInertia.map G.toFunctor (𝟭 C) (squareIso G) := sorry

/-- A based absolute-inertia map applies the original based functor to the underlying
object. -/
@[simp, stacks 04Z4 "absolute-inertia map object computation"]
theorem obj (G : S₁ ⥤ᵇ S₂) (A : (inertia S₁).obj) :
    ((Inertia.map G).toFunctor.obj A).obj = G.toFunctor.obj A.obj := sorry

/-- A based absolute-inertia map applies the original based functor to the chosen
automorphism. -/
@[simp, stacks 04Z4 "absolute-inertia map automorphism computation"]
theorem aut (G : S₁ ⥤ᵇ S₂) (A : (inertia S₁).obj) :
    ((Inertia.map G).toFunctor.obj A).aut = G.toFunctor.mapIso A.aut := sorry

/-- A based absolute-inertia map applies the original based functor to the underlying
arrow. -/
@[simp, stacks 04Z4 "absolute-inertia map underlying-arrow computation"]
theorem hom
    (G : S₁ ⥤ᵇ S₂) {A B : (inertia S₁).obj} (φ : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom ((Inertia.map G).toFunctor.map φ) =
      G.toFunctor.map (CategoryTheory.RelativeInertia.hom φ) := sorry

end Inertia.map

end BasedCategory
end CategoryTheory
