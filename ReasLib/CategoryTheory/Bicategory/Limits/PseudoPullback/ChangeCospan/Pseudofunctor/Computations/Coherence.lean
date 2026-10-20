/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Pseudofunctor.Computations.Map

/-!
# Coherence computations for readable change of cospan

This leaf exposes the identity and composition comparisons of
`changeCospan.pseudofunctor`, including their apex components.  It depends on the action leaf but
does not add another pseudofunctor owner.
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

/-- The unit comparison of readable change of cospan is `changeCospan.mapId`. -/
@[simp]
theorem changeCospan.pseudofunctor.mapId
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    (changeCospan.pseudofunctor ψ).mapId S =
      changeCospan.mapId ψ S := sorry
/- Proof strategy: unfold `changeCospan.pseudofunctor` and read its `mapId` field. -/

/-- The composition comparison of readable change of cospan is `changeCospan.mapComp`. -/
@[simp]
theorem changeCospan.pseudofunctor.mapComp
    (ψ : CospanTransform f g f' g')
    {R S T : PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    (changeCospan.pseudofunctor ψ).mapComp u v =
      changeCospan.mapComp ψ u v := sorry
/- Proof strategy: unfold `changeCospan.pseudofunctor` and read its `mapComp` field. -/

/-- The forward unit comparison of readable change of cospan has identity apex cell. -/
@[simp]
theorem changeCospan.pseudofunctor.mapId.hom.apex
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    PseudoPullbackCone.map₂
        ((changeCospan.pseudofunctor ψ).mapId S).hom =
      𝟙 (𝟙 S.pt) := sorry
/- Proof strategy: rewrite with `changeCospan.pseudofunctor.mapId` and
`changeCospan.mapId.hom.apex`. -/

/-- The inverse unit comparison of readable change of cospan has identity apex cell. -/
@[simp]
theorem changeCospan.pseudofunctor.mapId.inv.apex
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    PseudoPullbackCone.map₂
        ((changeCospan.pseudofunctor ψ).mapId S).inv =
      𝟙 (𝟙 S.pt) := sorry
/- Proof strategy: rewrite with `changeCospan.pseudofunctor.mapId` and
`changeCospan.mapId.inv.apex`. -/

/-- The forward composition comparison of readable change of cospan has identity apex cell. -/
@[simp]
theorem changeCospan.pseudofunctor.mapComp.hom.apex
    (ψ : CospanTransform f g f' g')
    {R S T : PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    PseudoPullbackCone.map₂
        ((changeCospan.pseudofunctor ψ).mapComp u v).hom =
      𝟙 (PseudoPullbackCone.map u ≫ PseudoPullbackCone.map v) := sorry
/- Proof strategy: rewrite with `changeCospan.pseudofunctor.mapComp` and
`changeCospan.mapComp.hom.apex`. -/

/-- The inverse composition comparison of readable change of cospan has identity apex cell. -/
@[simp]
theorem changeCospan.pseudofunctor.mapComp.inv.apex
    (ψ : CospanTransform f g f' g')
    {R S T : PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    PseudoPullbackCone.map₂
        ((changeCospan.pseudofunctor ψ).mapComp u v).inv =
      𝟙 (PseudoPullbackCone.map u ≫ PseudoPullbackCone.map v) := sorry
/- Proof strategy: rewrite with `changeCospan.pseudofunctor.mapComp` and
`changeCospan.mapComp.inv.apex`. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
