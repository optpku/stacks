module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Hom.Construction

/-!
# Computations for changed-cospan cone morphisms

This leaf contains only proposition-valued readouts for `fac`, `map`, and `map₂`.  Consumers that
construct changed-cospan morphisms can import `Hom.Construction` without loading these equations.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

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

/-- The left component of the changed-cospan morphism comparison is the generic
postcomposition component. -/
@[simp]
theorem changeCospan.fac.app_left
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    (changeCospan.fac ψ u).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      (PseudoCone.postcomposeFac ψ u.hom).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) := sorry

/-- The right component of the changed-cospan morphism comparison is the generic
postcomposition component. -/
@[simp]
theorem changeCospan.fac.app_right
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    (changeCospan.fac ψ u).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      (PseudoCone.postcomposeFac ψ u.hom).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) := sorry

/-- The central component of the changed-cospan morphism comparison is the explicit
readable/generic presentation conjugation. -/
@[simp]
theorem changeCospan.fac.app_base
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    (changeCospan.fac ψ u).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      PseudoPullbackCone.map u ◁
          (changeCospan.presentation.baseIso T ψ).hom ≫
        (PseudoCone.postcomposeFac ψ u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.one) ≫
        (changeCospan.presentation.baseIso S ψ).inv := sorry

/-- The first-leg comparison of a changed-cospan cone morphism is the original first-leg
comparison postcomposed with the left component of the cospan transformation. -/
@[simp]
theorem changeCospan.map.fstFac
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.fstFac (changeCospan.map ψ u) =
      (α_ (PseudoPullbackCone.map u) T.fst ψ.left).inv ≫
        PseudoPullbackCone.fstFac u ▷ ψ.left := sorry

/-- The second-leg comparison of a changed-cospan cone morphism is the original second-leg
comparison postcomposed with the right component of the cospan transformation. -/
@[simp]
theorem changeCospan.map.sndFac
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.sndFac (changeCospan.map ψ u) =
      (α_ (PseudoPullbackCone.map u) T.snd ψ.right).inv ≫
        PseudoPullbackCone.sndFac u ▷ ψ.right := sorry

/-- The central comparison of a changed-cospan cone morphism is obtained by transporting the
original central comparison through the two readable presentation isomorphisms. -/
@[simp]
theorem changeCospan.map.baseFac
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.baseFac (changeCospan.map ψ u) =
      PseudoPullbackCone.map u ◁
          (changeCospan.presentation.baseIso T ψ).hom ≫
        (α_ (PseudoPullbackCone.map u) (T.fst ≫ f) ψ.base).inv ≫
        PseudoPullbackCone.baseFac u ▷ ψ.base ≫
        (changeCospan.presentation.baseIso S ψ).inv := sorry

/-- Changing cospan leaves the apex map of a readable cone morphism unchanged. -/
@[simp]
theorem changeCospan.map.apex
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.map (changeCospan.map ψ u) =
      PseudoPullbackCone.map u := sorry

/-- The comparison modification of a changed-cospan cone morphism is `changeCospan.fac`. -/
@[simp]
theorem changeCospan.map.fac
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.fac (changeCospan.map ψ u) =
      changeCospan.fac ψ u := sorry

/-- Changing cospan leaves the apex cell of a readable cone `2`-morphism unchanged. -/
@[simp]
theorem changeCospan.map₂.apex
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    PseudoPullbackCone.map₂ (changeCospan.map₂ ψ η) =
      PseudoPullbackCone.map₂ η := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
