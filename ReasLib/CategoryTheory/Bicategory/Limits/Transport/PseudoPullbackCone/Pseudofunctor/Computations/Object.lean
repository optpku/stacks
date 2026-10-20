/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Pseudofunctor.Basic

/-!
# Object computations for readable pseudopullback-cone transport

This leaf exposes the apex, legs, and comparison isomorphism of a readable pseudopullback cone
transported by a pseudofunctor. It contains no morphism-action or coherence computations.
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

/-- The apex of an object transported by the readable pseudopullback-cone pseudofunctor. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.obj.pt (H : Pseudofunctor B D)
    (S : Bicategory.PseudoPullbackCone f g) :
    ((mapPseudoPullbackCone.pseudofunctor f g H).obj S).pt =
      H.obj S.pt := sorry

/-- The left leg of an object transported by the readable pseudopullback-cone
pseudofunctor. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.obj.fst
    (H : Pseudofunctor B D) (S : Bicategory.PseudoPullbackCone f g) :
    ((mapPseudoPullbackCone.pseudofunctor f g H).obj S).fst =
      H.map S.fst := sorry

/-- The right leg of an object transported by the readable pseudopullback-cone
pseudofunctor. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.obj.snd
    (H : Pseudofunctor B D) (S : Bicategory.PseudoPullbackCone f g) :
    ((mapPseudoPullbackCone.pseudofunctor f g H).obj S).snd =
      H.map S.snd := sorry

/-- The square comparison of an object transported by the readable pseudopullback-cone
pseudofunctor. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.obj.iso
    (H : Pseudofunctor B D) (S : Bicategory.PseudoPullbackCone f g) :
    ((mapPseudoPullbackCone.pseudofunctor f g H).obj S).iso =
      (H.mapComp S.fst f).symm ≪≫
        H.map₂Iso S.iso ≪≫ H.mapComp S.snd g := sorry

/-- The forward square cell of an object transported by the readable
pseudopullback-cone pseudofunctor. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.obj.iso.hom
    (H : Pseudofunctor B D) (S : Bicategory.PseudoPullbackCone f g) :
    ((mapPseudoPullbackCone.pseudofunctor f g H).obj S).iso.hom =
      (H.mapComp S.fst f).inv ≫
        H.map₂ S.iso.hom ≫ (H.mapComp S.snd g).hom := sorry

/-- The inverse square cell of an object transported by the readable
pseudopullback-cone pseudofunctor. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.obj.iso.inv
    (H : Pseudofunctor B D) (S : Bicategory.PseudoPullbackCone f g) :
    ((mapPseudoPullbackCone.pseudofunctor f g H).obj S).iso.inv =
      (H.mapComp S.snd g).inv ≫
        H.map₂ S.iso.inv ≫ (H.mapComp S.fst f).hom := sorry

end Pseudofunctor

end CategoryTheory
