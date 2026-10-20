/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Hom.Construction

/-!
# Composition coherence for changing cospan

This module records the composition comparison for the action of a walking-cospan
transformation on readable pseudopullback-cone morphisms.  The apex component remains an
identity cell, so the comparison isolates exactly the readable cone-presentation coherence.
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

namespace Implementation

/-- Compatibility of the forward composition comparison with changed-cospan cone
comparisons. -/
private theorem changeCospan.mapComp.hom_comm
    (ψ : CospanTransform f g f' g')
    {R S T : PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    ((T.changeCospan ψ).toPseudoCone.comparison R.pt).map
          (𝟙 (PseudoPullbackCone.map u ≫ PseudoPullbackCone.map v)) ≫
        PseudoPullbackCone.fac
          (changeCospan.map ψ u ≫ changeCospan.map ψ v) =
      PseudoPullbackCone.fac (changeCospan.map ψ (u ≫ v)) := sorry
/- Proof strategy: expand `changeCospan.fac`; cancel presentation isomorphisms and use the
generic `ColaxCostructuredArrow.postcompose.mapComp` comparison. -/

/-- The forward composition comparison for readable change of cospan. -/
private def changeCospan.mapComp.hom
    (ψ : CospanTransform f g f' g')
    {R S T : PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    changeCospan.map ψ (u ≫ v) ⟶
      changeCospan.map ψ u ≫ changeCospan.map ψ v :=
  PseudoPullbackCone.hom₂Mk
    (𝟙 (PseudoPullbackCone.map u ≫ PseudoPullbackCone.map v))
    (changeCospan.mapComp.hom_comm ψ u v)

/-- Compatibility of the inverse composition comparison with changed-cospan cone
comparisons. -/
private theorem changeCospan.mapComp.inv_comm
    (ψ : CospanTransform f g f' g')
    {R S T : PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    ((T.changeCospan ψ).toPseudoCone.comparison R.pt).map
          (𝟙 (PseudoPullbackCone.map u ≫ PseudoPullbackCone.map v)) ≫
        PseudoPullbackCone.fac (changeCospan.map ψ (u ≫ v)) =
      PseudoPullbackCone.fac
        (changeCospan.map ψ u ≫ changeCospan.map ψ v) := sorry
/- Proof strategy: use the inverse generic `ColaxCostructuredArrow.postcompose.mapComp` comparison through
the same presentation conjugations. -/

/-- The inverse composition comparison for readable change of cospan. -/
private def changeCospan.mapComp.inv
    (ψ : CospanTransform f g f' g')
    {R S T : PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    changeCospan.map ψ u ≫ changeCospan.map ψ v ⟶
      changeCospan.map ψ (u ≫ v) :=
  PseudoPullbackCone.hom₂Mk
    (𝟙 (PseudoPullbackCone.map u ≫ PseudoPullbackCone.map v))
    (changeCospan.mapComp.inv_comm ψ u v)

/-- The forward and inverse composition comparisons for readable change of cospan cancel on
the mapped composite. -/
private theorem changeCospan.mapComp.hom_inv_id
    (ψ : CospanTransform f g f' g')
    {R S T : PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    changeCospan.mapComp.hom ψ u v ≫
        changeCospan.mapComp.inv ψ u v =
      𝟙 (changeCospan.map ψ (u ≫ v)) := sorry
/- Proof strategy: apply `PseudoPullbackCone.hom₂_ext`; every apex component is an
identity. -/

/-- The inverse and forward composition comparisons for readable change of cospan cancel on
the composite of mapped morphisms. -/
private theorem changeCospan.mapComp.inv_hom_id
    (ψ : CospanTransform f g f' g')
    {R S T : PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    changeCospan.mapComp.inv ψ u v ≫
        changeCospan.mapComp.hom ψ u v =
      𝟙 (changeCospan.map ψ u ≫ changeCospan.map ψ v) := sorry
/- Proof strategy: apply `PseudoPullbackCone.hom₂_ext`; every apex component is an
identity. -/

end Implementation

/-- The composition comparison for readable change of cospan. Its apex component is an
explicit identity `2`-morphism. -/
def changeCospan.mapComp
    (ψ : CospanTransform f g f' g')
    {R S T : PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    changeCospan.map ψ (u ≫ v) ≅
      changeCospan.map ψ u ≫ changeCospan.map ψ v where
  hom := Implementation.changeCospan.mapComp.hom ψ u v
  inv := Implementation.changeCospan.mapComp.inv ψ u v
  hom_inv_id := Implementation.changeCospan.mapComp.hom_inv_id ψ u v
  inv_hom_id := Implementation.changeCospan.mapComp.inv_hom_id ψ u v

/-- The apex cell of the forward composition comparison for readable change of cospan is the
identity. -/
@[simp]
theorem changeCospan.mapComp.hom.apex
    (ψ : CospanTransform f g f' g')
    {R S T : PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    PseudoPullbackCone.map₂ (changeCospan.mapComp ψ u v).hom =
      𝟙 (PseudoPullbackCone.map u ≫ PseudoPullbackCone.map v) := sorry
/- Proof strategy: unfold `changeCospan.mapComp` and its forward helper, then apply
`PseudoPullbackCone.hom₂Mk_map₂`. -/

/-- The apex cell of the inverse composition comparison for readable change of cospan is the
identity. -/
@[simp]
theorem changeCospan.mapComp.inv.apex
    (ψ : CospanTransform f g f' g')
    {R S T : PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    PseudoPullbackCone.map₂ (changeCospan.mapComp ψ u v).inv =
      𝟙 (PseudoPullbackCone.map u ≫ PseudoPullbackCone.map v) := sorry
/- Proof strategy: unfold `changeCospan.mapComp` and its inverse helper, then apply
`PseudoPullbackCone.hom₂Mk_map₂`. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
