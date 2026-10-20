/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PullbackConditions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.BaseChange

/-!
# Pullbacks of elementary étale neighbourhoods

Elementary étale neighbourhoods give unique pointed lifts through fibre products,
with concrete scheme and Zariski stalk maps between subsequent neighbourhoods.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
variable (f : X ⟶ Y) {x : Points X} (V : Elementary Y (Points.map f x))

/-- A point of `pullback f V.obj.hom` lies over the pair `(x, V.obj.point)`. -/
def isLift (x' : Points (pullback f V.obj.hom)) : Prop :=
  Points.map (pullback.fst f V.obj.hom) x' = x ∧
    Points.map (pullback.snd f V.obj.hom) x' =
      ofOver.pointsEquiv V.obj.toOver V.obj.point

/-- The fibre condition `isLift` is the conjunction of the two projection
equations. -/
theorem isLift_iff (x' : Points (pullback f V.obj.hom)) :
    isLift f V x' ↔
      Points.map (pullback.fst f V.obj.hom) x' = x ∧
        Points.map (pullback.snd f V.obj.hom) x' =
          ofOver.pointsEquiv V.obj.toOver V.obj.point :=
  sorry

/-- Uniqueness of the fibre point of `pullback f V.obj.hom` over
`(x, V.obj.point)`. -/
theorem uniqueLift_eq {x₁ x₂ : Points (pullback f V.obj.hom)}
    (hx₁ : isLift f V x₁) (hx₂ : isLift f V x₂) :
    x₁ = x₂ :=
  sorry


/-- The pullback of an elementary étale neighbourhood has a unique point over
the chosen point and the selected neighbourhood point. -/
theorem uniqueLift :
    ∃! x' : Points (pullback f V.obj.hom), isLift f V x' :=
  sorry

variable {x' : Points (pullback f V.obj.hom)}
variable (U : Elementary (pullback f V.obj.hom) x')

/-- The scheme morphism `U ⟶ V` over `Y` associated to an elementary neighbourhood
of a point of `V ×_Y X`. -/
def schemeHomToBase : U.obj.scheme ⟶ V.obj.scheme :=
  (Yoneda.fullyFaithful.preimage
    (U.obj.hom ≫ pullback.snd f V.obj.hom :
      yoneda.obj U.obj.toOver ⟶ yoneda.obj V.obj.toOver)).left

/-- `schemeHomToBase` sends the selected point of `U` to that of `V` when `x'` is
a lift of `(x, V.obj.point)`, and the induced algebraic-space morphism is a
morphism over `Y`. -/
theorem schemeHomToBase_spec (hx' : isLift f V x') :
    schemeHomToBase f V U U.obj.point = V.obj.point ∧
      ofOverMap (Yoneda.fullyFaithful.preimage
        (U.obj.hom ≫ pullback.snd f V.obj.hom :
          yoneda.obj U.obj.toOver ⟶ yoneda.obj V.obj.toOver)) ≫ V.obj.hom =
        U.obj.hom ≫ pullback.snd f V.obj.hom ≫ V.obj.hom :=
  sorry

/-- The stalk map of `schemeHomToBase` transported to the selected point of `V`. -/
def schemeHomToBase_stalkMap
    (hpoint : schemeHomToBase f V U U.obj.point = V.obj.point) :
    (V.obj.scheme).presheaf.stalk V.obj.point ⟶
      (U.obj.scheme).presheaf.stalk U.obj.point :=
  hpoint ▸ (schemeHomToBase f V U).stalkMap U.obj.point

/-- `schemeHomToBase_stalkMap` is the stalk map of `schemeHomToBase` after identifying
the image of `U.obj.point` with `V.obj.point`. -/
theorem schemeHomToBase_stalkMap_eq
    (hpoint : schemeHomToBase f V U U.obj.point = V.obj.point) :
    schemeHomToBase_stalkMap f V U hpoint =
      hpoint ▸ (schemeHomToBase f V U).stalkMap U.obj.point :=
  sorry

/-- The underlying ring homomorphism of `schemeHomToBase_stalkMap`. -/
def schemeHomToBase_stalkHom
    (hpoint : schemeHomToBase f V U U.obj.point = V.obj.point) :
    (V.obj.scheme).presheaf.stalk V.obj.point →+*
      (U.obj.scheme).presheaf.stalk U.obj.point :=
  CommRingCat.Hom.hom (schemeHomToBase_stalkMap f V U hpoint)

/-- `schemeHomToBase_stalkHom` is local, as a stalk map of schemes. -/
instance schemeHomToBase_stalkHom_isLocalHom
    (hpoint : schemeHomToBase f V U U.obj.point = V.obj.point) :
    IsLocalHom (schemeHomToBase_stalkHom f V U hpoint) :=
  sorry

/-- The Zariski-stalk `Spec` square of `schemeHomToBase` at the selected points
`u` and `v` commutes. -/
theorem fromSpecStalk_commSq (hx' : isLift f V x')
    (hpoint : schemeHomToBase f V U U.obj.point = V.obj.point) :
    CommSq (Spec.map (schemeHomToBase_stalkMap f V U hpoint))
      (Scheme.fromSpecStalk U.obj.scheme U.obj.point)
      (Scheme.fromSpecStalk V.obj.scheme V.obj.point)
      (schemeHomToBase f V U) :=
  sorry


/-- The neighbourhood morphism over the pullback gives a commutative square
with the original morphism of algebraic spaces. -/
theorem space_commSq (hx' : isLift f V x') :
    CommSq (U.obj.hom ≫ pullback.snd f V.obj.hom)
      (U.obj.hom ≫ pullback.fst f V.obj.hom) V.obj.hom f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood
