/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category

/-! # Cartesian morphisms of families of curves -/

@[expose] public section

-- Local declaration justification (metaprogramming implementation): exposed data definitions
-- must reference their private construction and projection laws under Lean's module visibility rules.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

private def homMkRaw {S : Scheme.{u}} {P Q : Obj S} (left : space P ⟶ space Q)
    (right : base P ⟶ base Q)
    (w : left ≫ hom Q = hom P ≫ (ofOverFunctor S).map right) :
    P.obj.obj.obj ⟶ Q.obj.obj.obj :=
  { hom := { left := left, right := right, w := w } }

private theorem homMk_stronglyCartesian {S : Scheme.{u}} {P Q : Obj S}
    (left : space P ⟶ space Q) (right : base P ⟶ base Q)
    (w : left ≫ hom Q = hom P ≫ (ofOverFunctor S).map right)
    (sq : IsPullback left (hom P) (hom Q) ((ofOverFunctor S).map right)) :
    Functor.IsStronglyCartesian.property ((finiteType S).ι ⋙ Spaces.p)
      (homMkRaw left right w) := sorry

/-- A cartesian square of curve families defines a morphism in the category of curves. -/
def homMk {S : Scheme.{u}} {P Q : Obj S} (left : space P ⟶ space Q)
    (right : base P ⟶ base Q)
    (w : left ≫ hom Q = hom P ≫ (ofOverFunctor S).map right)
    (sq : IsPullback left (hom P) (hom Q) ((ofOverFunctor S).map right)) : P ⟶ Q :=
  { hom := { hom := ⟨homMkRaw left right w, homMk_stronglyCartesian left right w sq⟩ } }

/-- The total-space component of the cartesian-square constructor is the supplied map. -/
theorem homMk_left {S : Scheme.{u}} {P Q : Obj S} (left : space P ⟶ space Q)
    (right : base P ⟶ base Q)
    (w : left ≫ hom Q = hom P ≫ (ofOverFunctor S).map right)
    (sq : IsPullback left (hom P) (hom Q) ((ofOverFunctor S).map right)) :
    spaceMap (homMk left right w sq) = left := rfl

/-- The base component of the cartesian-square constructor is the supplied map. -/
theorem homMk_right {S : Scheme.{u}} {P Q : Obj S} (left : space P ⟶ space Q)
    (right : base P ⟶ base Q)
    (w : left ≫ hom Q = hom P ≫ (ofOverFunctor S).map right)
    (sq : IsPullback left (hom P) (hom Q) ((ofOverFunctor S).map right)) :
    baseMap (homMk left right w sq) = right := rfl

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
