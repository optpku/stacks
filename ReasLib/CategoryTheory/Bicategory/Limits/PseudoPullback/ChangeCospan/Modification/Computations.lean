module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Modification.Construction

/-!
# Computations for modifications acting on readable changed-cospan cones

This leaf contains the vertexwise component formulas for the explicit
`changeCospan.modification` action. Identity and vertical-composition laws are kept in
`Modification.Functoriality` so ordinary-functor construction does not load these readouts.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- At every walking-cospan vertex, `changeCospan.modification` is the generic whiskered
component conjugated by the two presentation comparisons. -/
@[simp]
theorem changeCospan.modification.app
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    (S : PseudoPullbackCone f g)
    (j : LocallyDiscrete Limits.WalkingCospan) :
    (changeCospan.modification Γ S).as.app j =
      (changeCospan.presentation.iso S ψ j).hom ≫
        S.toPseudoCone.π.app j ◁ Γ.as.app j ≫
        (changeCospan.presentation.iso S φ j).inv := sorry

/-- At the left endpoint, change of cospan acts by left whiskering the left component of
the cospan modification with the first projection. -/
@[simp]
theorem changeCospan.modification.app_left
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    (S : PseudoPullbackCone f g) :
    (changeCospan.modification Γ S).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      S.fst ◁ CospanTransform.Hom.left Γ := sorry

/-- At the right endpoint, change of cospan acts by left whiskering the right component of
the cospan modification with the second projection. -/
@[simp]
theorem changeCospan.modification.app_right
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    (S : PseudoPullbackCone f g) :
    (changeCospan.modification Γ S).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      S.snd ◁ CospanTransform.Hom.right Γ := sorry

/-- At the central vertex, the base component of the cospan modification is conjugated by
the two central presentation comparisons. -/
@[simp]
theorem changeCospan.modification.app_base
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    (S : PseudoPullbackCone f g) :
    (changeCospan.modification Γ S).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      (changeCospan.presentation.baseIso S ψ).hom ≫
        (S.fst ≫ f) ◁ CospanTransform.Hom.base Γ ≫
        (changeCospan.presentation.baseIso S φ).inv := sorry

/- The declarations in this leaf are proposition-valued readouts and introduce no additional
modification data. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
