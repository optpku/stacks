module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap68.Remark_68_11_11_Pullback

/-!
# Scheme morphisms of elementary neighbourhoods over a pullback

An elementary étale neighbourhood of the unique lift of `(x, v)` on
`V ×_Y X` determines a scheme morphism `U ⟶ V` over `Y`, together with the
induced stalk map at the selected points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
variable (f : X ⟶ Y) {x : Points X} (V : Elementary Y (Points.map f x))
variable {x' : Points (pullback f V.obj.hom)}
variable (U : Elementary (pullback f V.obj.hom) x')

/-- The scheme morphism `U ⟶ V` over `Y` associated to an elementary neighbourhood
of a point of `V ×_Y X`. -/
def schemeHomToBase : U.obj.scheme ⟶ V.obj.scheme :=
  (toOverHom (U.obj.hom ≫ pullback.snd f V.obj.hom)).left

/-- `schemeHomToBase` sends the selected point of `U` to that of `V` when `x'` is
a lift of `(x, V.obj.point)`, and the induced algebraic-space morphism is a
morphism over `Y`. -/
theorem schemeHomToBase_spec (hx' : isLift f V x') :
    schemeHomToBase f V U U.obj.point = V.obj.point ∧
      ofOverMap (toOverHom (U.obj.hom ≫ pullback.snd f V.obj.hom)) ≫ V.obj.hom =
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
theorem schemeHomToBase_stalkHom_isLocalHom
    (hpoint : schemeHomToBase f V U U.obj.point = V.obj.point) :
    IsLocalHom (schemeHomToBase_stalkHom f V U hpoint) :=
  sorry

/-- The Zariski-stalk `Spec` square of `schemeHomToBase` at the selected points
`u` and `v`, as in `Scheme.SpecMap_stalkMap_fromSpecStalk`. -/
theorem fromSpecStalk_commSq (hx' : isLift f V x')
    (hpoint : schemeHomToBase f V U U.obj.point = V.obj.point) :
    CommSq (Spec.map (schemeHomToBase_stalkMap f V U hpoint))
      (Scheme.fromSpecStalk U.obj.scheme U.obj.point)
      (Scheme.fromSpecStalk V.obj.scheme V.obj.point)
      (schemeHomToBase f V U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood
