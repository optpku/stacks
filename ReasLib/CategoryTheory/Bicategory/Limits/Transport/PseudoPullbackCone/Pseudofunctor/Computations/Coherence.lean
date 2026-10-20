/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Pseudofunctor.Computations.Map

/-!
# Coherence computations for readable pseudopullback-cone transport

This leaf exposes the apex components of the identity and composition comparisons of the
readable cone transport pseudofunctor.
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

/-- The forward unit comparison of readable cone transport has apex cell `H.mapId`. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.mapId.hom.apex
    (H : Pseudofunctor B D) (S : Bicategory.PseudoPullbackCone f g) :
    Bicategory.PseudoPullbackCone.map₂
        ((mapPseudoPullbackCone.pseudofunctor f g H).mapId S).hom =
      (H.mapId S.pt).hom := sorry

/-- The inverse unit comparison of readable cone transport has the inverse apex cell of
`H.mapId`. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.mapId.inv.apex
    (H : Pseudofunctor B D) (S : Bicategory.PseudoPullbackCone f g) :
    Bicategory.PseudoPullbackCone.map₂
        ((mapPseudoPullbackCone.pseudofunctor f g H).mapId S).inv =
      (H.mapId S.pt).inv := sorry

/-- The forward composition comparison of readable cone transport has apex cell
`H.mapComp`. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.mapComp.hom.apex
    (H : Pseudofunctor B D)
    {R S T : Bicategory.PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    Bicategory.PseudoPullbackCone.map₂
        ((mapPseudoPullbackCone.pseudofunctor f g H).mapComp u v).hom =
      (H.mapComp (Bicategory.PseudoPullbackCone.map u)
        (Bicategory.PseudoPullbackCone.map v)).hom := sorry

/-- The inverse composition comparison of readable cone transport has the inverse apex cell of
`H.mapComp`. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.mapComp.inv.apex
    (H : Pseudofunctor B D)
    {R S T : Bicategory.PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    Bicategory.PseudoPullbackCone.map₂
        ((mapPseudoPullbackCone.pseudofunctor f g H).mapComp u v).inv =
      (H.mapComp (Bicategory.PseudoPullbackCone.map u)
        (Bicategory.PseudoPullbackCone.map v)).inv := sorry

end Pseudofunctor

end CategoryTheory
