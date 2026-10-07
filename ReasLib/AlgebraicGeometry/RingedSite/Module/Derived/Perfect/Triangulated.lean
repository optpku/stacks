module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect

@[expose] public section

/-!
# Triangulated closure of perfect derived module sheaves

This module records that perfect derived module sheaves on a bundled ringed site form a
triangulated object property.  The three objectwise distinguished-triangle consequences are
provided alongside the canonical `ObjectProperty.IsTriangulated` instance.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open RingedSite.Hom (ModuleDerived)

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

section

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [∀ U : X,
  HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Perfect objects of `D(𝒪_X)` form a triangulated object property. -/
@[stacks 08G9]
instance isPerfect_isTriangulated :
    ObjectProperty.IsTriangulated
      (IsPerfect : ObjectProperty (ModuleDerived.{w} X)) := sorry

/-- In a distinguished triangle in `D(𝒪_X)`, perfectness of the first two
objects implies perfectness of the third. -/
@[stacks 08G9]
theorem isPerfect_obj₃_of_distinguished_triangle
    (T : Triangle (ModuleDerived.{w} X)) (hT : T ∈ distTriang (ModuleDerived.{w} X))
    (h₁ : IsPerfect T.obj₁) (h₂ : IsPerfect T.obj₂) :
    IsPerfect T.obj₃ := sorry

/-- In a distinguished triangle in `D(𝒪_X)`, perfectness of the first and
third objects implies perfectness of the second. -/
@[stacks 08G9]
theorem isPerfect_obj₂_of_distinguished_triangle
    (T : Triangle (ModuleDerived.{w} X)) (hT : T ∈ distTriang (ModuleDerived.{w} X))
    (h₁ : IsPerfect T.obj₁) (h₃ : IsPerfect T.obj₃) :
    IsPerfect T.obj₂ := sorry

/-- In a distinguished triangle in `D(𝒪_X)`, perfectness of the second and
third objects implies perfectness of the first. -/
@[stacks 08G9]
theorem isPerfect_obj₁_of_distinguished_triangle
    (T : Triangle (ModuleDerived.{w} X)) (hT : T ∈ distTriang (ModuleDerived.{w} X))
    (h₂ : IsPerfect T.obj₂) (h₃ : IsPerfect T.obj₃) :
    IsPerfect T.obj₁ := sorry

end

end RingedSite.Hom.ModuleDerived
