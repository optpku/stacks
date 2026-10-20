/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Pseudofunctor.Computations.Object

/-!
# Map computations for readable pseudopullback-cone transport

This leaf exposes the action on readable cone morphisms and cone `2`-morphisms, including all
three walking-cospan comparison components. Pseudofunctor coherence computations are downstream.
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

/-- Mapping a readable cone morphism transports its central comparison by conjugating the
generic mapped comparison with the central presentation isomorphisms. -/
@[simp]
theorem mapPseudoPullbackCone.map.baseFac (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.baseFac
        (mapPseudoPullbackCone.map H u) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.centerIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.one) ≫
        (mapPseudoPullbackCone.presentation.centerIso H S).inv := sorry

/-- The apex map underlying the image of a readable pseudopullback-cone morphism. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.map.apex (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.map
        ((mapPseudoPullbackCone.pseudofunctor f g H).map u) =
      H.map (Bicategory.PseudoPullbackCone.map u) := sorry

/-- The comparison modification underlying the image of a readable
pseudopullback-cone morphism. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.map.fac (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.fac
        ((mapPseudoPullbackCone.pseudofunctor f g H).map u) =
      mapPseudoPullbackCone.fac H u := sorry

/-- Mapping a readable cone morphism transports its left-leg comparison by `H.map₂`, after
undoing the composition comparison of `H`. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.map.fstFac
    (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.fstFac
        ((mapPseudoPullbackCone.pseudofunctor f g H).map u) =
      (H.mapComp (Bicategory.PseudoPullbackCone.map u) T.fst).inv ≫
        H.map₂ (Bicategory.PseudoPullbackCone.fstFac u) := sorry

/-- Mapping a readable cone morphism transports its right-leg comparison by `H.map₂`, after
undoing the composition comparison of `H`. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.map.sndFac
    (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.sndFac
        ((mapPseudoPullbackCone.pseudofunctor f g H).map u) =
      (H.mapComp (Bicategory.PseudoPullbackCone.map u) T.snd).inv ≫
        H.map₂ (Bicategory.PseudoPullbackCone.sndFac u) := sorry

/-- The central comparison of a morphism transported by the readable cone pseudofunctor is the
central comparison of the canonical mapped cone morphism. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.map.baseFac
    (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.baseFac
        ((mapPseudoPullbackCone.pseudofunctor f g H).map u) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.centerIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.one) ≫
        (mapPseudoPullbackCone.presentation.centerIso H S).inv := sorry

/-- The apex cell underlying the image of a readable pseudopullback-cone `2`-morphism. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.map₂.apex
    (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g}
    {u v : S ⟶ T} (η : u ⟶ v) :
    Bicategory.PseudoPullbackCone.map₂
        ((mapPseudoPullbackCone.pseudofunctor f g H).map₂ η) =
      H.map₂ (Bicategory.PseudoPullbackCone.map₂ η) := sorry

end Pseudofunctor

end CategoryTheory
