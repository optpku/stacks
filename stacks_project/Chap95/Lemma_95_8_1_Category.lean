module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Fibered.FullSubcategory.Stack
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap95.«95_7_0_1_Spaces»

/-!
# Finite-type algebraic spaces over schemes

The full subcategory of `Spaces` on pairs `X / U` whose structure morphism is of
finite type, together with the restricted projection `p_ft`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

namespace FiniteType

/-- Objects of `Spaces` whose structure morphism is of finite type. -/
def objectProperty (S : Scheme.{u}) : ObjectProperty (Spaces S) :=
  fun P ↦ FiniteType P.hom

/-- Membership in the finite-type cut is finite type of the structure morphism. -/
theorem objectProperty_iff (S : Scheme.{u}) (P : Spaces S) :
    objectProperty S P ↔ FiniteType P.hom :=
  sorry

/-- Package a finite-type morphism `X ⟶ ofOver U` as an object of the full
subcategory. -/
def mk {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FiniteType pX] :
    (objectProperty S).FullSubcategory where
  obj := Spaces.mk pX
  property := (inferInstance : FiniteType pX)

/-- The underlying object of `mk pX` is `Spaces.mk pX`. -/
theorem mk_obj {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FiniteType pX] :
    (mk pX).obj = Spaces.mk pX :=
  sorry

/-- Objects of the finite-type full subcategory have finite-type structure
morphisms. -/
instance instFiniteType {S : Scheme.{u}}
    (x : (objectProperty S).FullSubcategory) :
    FiniteType x.obj.hom :=
  x.property

/-- The inclusion of finite-type objects into `Spaces`. -/
abbrev inclusion (S : Scheme.{u}) :
    (objectProperty S).FullSubcategory ⥤ Spaces S :=
  (objectProperty S).ι

/-- The functor `p_ft` is the restriction of `Spaces.p` to the finite-type full
subcategory. -/
def p (S : Scheme.{u}) : (objectProperty S).FullSubcategory ⥤ Over S :=
  (objectProperty S).ι ⋙ (Spaces.p : Spaces S ⥤ Over S)

/-- The restricted projection is the inclusion followed by `Spaces.p`. -/
theorem inclusion_comp_p (S : Scheme.{u}) :
    inclusion S ⋙ (Spaces.p : Spaces S ⥤ Over S) = p S :=
  sorry

/-- The object part of `p_ft` sends `mk pX` to the scheme `U` over `S`. -/
theorem p_obj {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FiniteType pX] : (p S).obj (mk pX) = U :=
  sorry

/-- The morphism part of `p_ft` is the underlying morphism of schemes over `S`. -/
theorem p_map {S : Scheme.{u}} {x y : (objectProperty S).FullSubcategory}
    (φ : x ⟶ y) : (p S).map φ = φ.hom.right :=
  sorry

/-- Finite type of structure morphisms is stable under strongly cartesian
pullback in `Spaces`. -/
theorem cartesianPullback (S : Scheme.{u}) :
    ObjectProperty.IsStableUnder.CartesianPullback (objectProperty S)
      (Spaces.p : Spaces S ⥤ Over S) :=
  sorry

end FiniteType

end AlgebraicGeometry.AlgebraicSpace.Spaces
