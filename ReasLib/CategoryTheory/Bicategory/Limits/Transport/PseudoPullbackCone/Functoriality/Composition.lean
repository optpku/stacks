/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Hom

/-!
# Composition comparison for readable pseudopullback-cone transport

This module constructs the composition comparison for mapping readable pseudopullback cones
along a pseudofunctor. Its apex component is exactly the ambient pseudofunctor's `mapComp`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uD vD wD

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} {D : Type uD}
variable [Bicategory.{wB, vB} B] [Bicategory.{wD, vD} D]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

namespace Implementation

/-- Compatibility of the forward composition comparison with the readable mapped cone
comparisons. -/
private theorem mapPseudoPullbackCone.mapComp.hom.comm (H : Pseudofunctor B D)
    {R S T : Bicategory.PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    ((H.mapPseudoPullbackCone T).toPseudoCone.comparison
        (H.obj R.pt)).map
          (H.mapComp (Bicategory.PseudoPullbackCone.map u)
            (Bicategory.PseudoPullbackCone.map v)).hom ≫
        Bicategory.PseudoPullbackCone.fac
          (mapPseudoPullbackCone.map H u ≫
            mapPseudoPullbackCone.map H v) =
      Bicategory.PseudoPullbackCone.fac
        (mapPseudoPullbackCone.map H (u ≫ v)) := sorry

/-- The forward composition comparison between mapped readable pseudopullback-cone
morphisms. -/
private def mapPseudoPullbackCone.mapComp.hom (H : Pseudofunctor B D)
    {R S T : Bicategory.PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    mapPseudoPullbackCone.map H (u ≫ v) ⟶
      mapPseudoPullbackCone.map H u ≫
        mapPseudoPullbackCone.map H v :=
  Bicategory.PseudoPullbackCone.hom₂Mk
    (H.mapComp (Bicategory.PseudoPullbackCone.map u)
      (Bicategory.PseudoPullbackCone.map v)).hom
    (mapPseudoPullbackCone.mapComp.hom.comm H u v)

/-- Compatibility of the inverse composition comparison with the readable mapped cone
comparisons. -/
private theorem mapPseudoPullbackCone.mapComp.inv.comm (H : Pseudofunctor B D)
    {R S T : Bicategory.PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    ((H.mapPseudoPullbackCone T).toPseudoCone.comparison
        (H.obj R.pt)).map
          (H.mapComp (Bicategory.PseudoPullbackCone.map u)
            (Bicategory.PseudoPullbackCone.map v)).inv ≫
        Bicategory.PseudoPullbackCone.fac
          (mapPseudoPullbackCone.map H (u ≫ v)) =
      Bicategory.PseudoPullbackCone.fac
        (mapPseudoPullbackCone.map H u ≫
          mapPseudoPullbackCone.map H v) := sorry

/-- The inverse composition comparison between mapped readable pseudopullback-cone
morphisms. -/
private def mapPseudoPullbackCone.mapComp.inv (H : Pseudofunctor B D)
    {R S T : Bicategory.PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    mapPseudoPullbackCone.map H u ≫
        mapPseudoPullbackCone.map H v ⟶
      mapPseudoPullbackCone.map H (u ≫ v) :=
  Bicategory.PseudoPullbackCone.hom₂Mk
    (H.mapComp (Bicategory.PseudoPullbackCone.map u)
      (Bicategory.PseudoPullbackCone.map v)).inv
    (mapPseudoPullbackCone.mapComp.inv.comm H u v)

/-- The forward and inverse readable composition comparisons cancel on the mapped
composite. -/
private theorem mapPseudoPullbackCone.mapComp.homInvId
    (H : Pseudofunctor B D)
    {R S T : Bicategory.PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    mapPseudoPullbackCone.mapComp.hom H u v ≫
        mapPseudoPullbackCone.mapComp.inv H u v =
      𝟙 (mapPseudoPullbackCone.map H (u ≫ v)) := sorry

/-- The inverse and forward readable composition comparisons cancel on the composite of
mapped morphisms. -/
private theorem mapPseudoPullbackCone.mapComp.invHomId
    (H : Pseudofunctor B D)
    {R S T : Bicategory.PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    mapPseudoPullbackCone.mapComp.inv H u v ≫
        mapPseudoPullbackCone.mapComp.hom H u v =
      𝟙 (mapPseudoPullbackCone.map H u ≫
        mapPseudoPullbackCone.map H v) := sorry

end Implementation

/-- The composition comparison for mapping readable pseudopullback cones along a pseudofunctor.
Its apex component is the composition comparison of the ambient pseudofunctor. -/
def mapPseudoPullbackCone.mapComp (H : Pseudofunctor B D)
    {R S T : Bicategory.PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    mapPseudoPullbackCone.map H (u ≫ v) ≅
      mapPseudoPullbackCone.map H u ≫
        mapPseudoPullbackCone.map H v where
  hom := Implementation.mapPseudoPullbackCone.mapComp.hom H u v
  inv := Implementation.mapPseudoPullbackCone.mapComp.inv H u v
  hom_inv_id :=
    Implementation.mapPseudoPullbackCone.mapComp.homInvId H u v
  inv_hom_id :=
    Implementation.mapPseudoPullbackCone.mapComp.invHomId H u v

/-- The apex cell of the forward composition comparison is `H.mapComp`. -/
@[simp]
theorem mapPseudoPullbackCone.mapComp.hom.apex (H : Pseudofunctor B D)
    {R S T : Bicategory.PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    Bicategory.PseudoPullbackCone.map₂
        (mapPseudoPullbackCone.mapComp H u v).hom =
      (H.mapComp (Bicategory.PseudoPullbackCone.map u)
        (Bicategory.PseudoPullbackCone.map v)).hom := sorry

/-- The apex cell of the inverse composition comparison is the inverse of `H.mapComp`. -/
@[simp]
theorem mapPseudoPullbackCone.mapComp.inv.apex (H : Pseudofunctor B D)
    {R S T : Bicategory.PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    Bicategory.PseudoPullbackCone.map₂
        (mapPseudoPullbackCone.mapComp H u v).inv =
      (H.mapComp (Bicategory.PseudoPullbackCone.map u)
        (Bicategory.PseudoPullbackCone.map v)).inv := sorry

-- Data audit: the forward and inverse apex cells of `mapPseudoPullbackCone.mapComp` are
-- explicitly the two directions of `H.mapComp`; `sorryAx` is confined to compatibility and
-- inverse-law propositions.

end Pseudofunctor

end CategoryTheory
