/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Pseudofunctor.Basic

/-!
# Object computations for readable change of cospan

This leaf exposes the object action of `changeCospan.pseudofunctor` and the resulting apex,
legs, and comparison isomorphism.  Morphism and coherence calculations live in the sibling
`Map` and `Coherence` leaves.
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

/-- The object action of readable change of cospan is `PseudoPullbackCone.changeCospan`. -/
@[simp]
theorem changeCospan.pseudofunctor.obj
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    (changeCospan.pseudofunctor ψ).obj S =
      S.changeCospan ψ := sorry
/- Proof strategy: unfold `changeCospan.pseudofunctor` and its explicit prelax core. -/

/-- The apex of a readable pseudo-pullback cone after changing cospan. -/
@[simp]
theorem changeCospan.pseudofunctor.obj.pt
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    ((changeCospan.pseudofunctor ψ).obj S).pt = S.pt := sorry
/- Proof strategy: rewrite with `changeCospan.pseudofunctor.obj` and `changeCospan.pt`. -/

/-- The left projection of a readable pseudo-pullback cone after changing cospan. -/
@[simp]
theorem changeCospan.pseudofunctor.obj.fst
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    ((changeCospan.pseudofunctor ψ).obj S).fst =
      S.fst ≫ ψ.left := sorry
/- Proof strategy: rewrite with `changeCospan.pseudofunctor.obj` and `changeCospan.fst`. -/

/-- The right projection of a readable pseudo-pullback cone after changing cospan. -/
@[simp]
theorem changeCospan.pseudofunctor.obj.snd
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    ((changeCospan.pseudofunctor ψ).obj S).snd =
      S.snd ≫ ψ.right := sorry
/- Proof strategy: rewrite with `changeCospan.pseudofunctor.obj` and `changeCospan.snd`. -/

/-- The square comparison of a readable pseudo-pullback cone after changing cospan. -/
@[simp]
theorem changeCospan.pseudofunctor.obj.iso
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    ((changeCospan.pseudofunctor ψ).obj S).iso =
      α_ S.fst ψ.left f' ≪≫
        Bicategory.whiskerLeftIso S.fst ψ.leftIso ≪≫
        (α_ S.fst f ψ.base).symm ≪≫
        Bicategory.whiskerRightIso S.iso ψ.base ≪≫
        α_ S.snd g ψ.base ≪≫
        Bicategory.whiskerLeftIso S.snd ψ.rightIso.symm ≪≫
        (α_ S.snd ψ.right g').symm := sorry
/- Proof strategy: rewrite with `changeCospan.pseudofunctor.obj` and `changeCospan.iso`. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
