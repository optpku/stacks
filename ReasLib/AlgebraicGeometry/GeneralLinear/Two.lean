/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GeneralLinear.FirstRow
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.AffinePlane
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Surjective

/-!
# The general linear scheme of rank two

Coordinates are indexed by matrix positions, rather than an unrelated four-element type. The
first row gives explicit compatible morphisms to the affine plane, punctured affine plane, and
projective line.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

noncomputable section

universe u

namespace GLTwo

section CommRing

variable (k : Type u) [CommRing k]

/-- The universe-lifted matrix index used by the relative affine-space model of `GL₂`. -/
@[stacks 01KX "rank-two matrix index"]
abbrev index : Type u := ULift.{u} (Fin 2)

/-- The polynomial coordinate ring `k[a,b,c,d]`, indexed by positions of a `2 × 2` matrix. -/
@[stacks 01KX "rank-two polynomial coordinate ring"]
abbrev polynomialRing : Type u := GeneralLinear.polynomialRing k (index)

/-- The upper-left matrix coordinate `a`. -/
@[stacks 01KX "rank-two matrix coordinate a"]
abbrev a : polynomialRing k :=
  GeneralLinear.coordinate k (index) (ULift.up 0) (ULift.up 0)

/-- The upper-right matrix coordinate `b`. -/
@[stacks 01KX "rank-two matrix coordinate b"]
abbrev b : polynomialRing k :=
  GeneralLinear.coordinate k (index) (ULift.up 0) (ULift.up 1)

/-- The lower-left matrix coordinate `c`. -/
@[stacks 01KX "rank-two matrix coordinate c"]
abbrev c : polynomialRing k :=
  GeneralLinear.coordinate k (index) (ULift.up 1) (ULift.up 0)

/-- The lower-right matrix coordinate `d`. -/
@[stacks 01KX "rank-two matrix coordinate d"]
abbrev d : polynomialRing k :=
  GeneralLinear.coordinate k (index) (ULift.up 1) (ULift.up 1)

/-- The determinant `ad - bc` of the generic `2 × 2` matrix. -/
@[stacks 01KX "rank-two determinant"]
abbrev det : polynomialRing k := GeneralLinear.determinant k (index)

/-- In rank two, the generic determinant is `ad - bc`. -/
@[stacks 01KX "rank-two determinant formula"]
theorem det_eq_ad_sub_bc : det k = a k * d k - b k * c k := sorry

/-- The coordinate ring `k[a,b,c,d,1/(ad-bc)]` of `GL₂`. -/
@[stacks 01KX "rank-two general-linear coordinate ring"]
abbrev coordinateRing : Type u := GeneralLinear.coordinateRing k (index)

/-- The localized upper-left coordinate. -/
@[stacks 01KX "rank-two localized coordinate a"]
abbrev localizedA : coordinateRing k :=
  GeneralLinear.localizedCoordinate k (index) (ULift.up 0) (ULift.up 0)

/-- The localized upper-right coordinate. -/
@[stacks 01KX "rank-two localized coordinate b"]
abbrev localizedB : coordinateRing k :=
  GeneralLinear.localizedCoordinate k (index) (ULift.up 0) (ULift.up 1)

/-- The localized lower-left coordinate. -/
@[stacks 01KX "rank-two localized coordinate c"]
abbrev localizedC : coordinateRing k :=
  GeneralLinear.localizedCoordinate k (index) (ULift.up 1) (ULift.up 0)

/-- The localized lower-right coordinate. -/
@[stacks 01KX "rank-two localized coordinate d"]
abbrev localizedD : coordinateRing k :=
  GeneralLinear.localizedCoordinate k (index) (ULift.up 1) (ULift.up 1)

/-- The image of the generic determinant in the coordinate ring of `GL₂`. -/
@[stacks 01KX "rank-two localized determinant"]
abbrev localizedDeterminant : coordinateRing k :=
  algebraMap (polynomialRing k) (coordinateRing k) (det k)

/-- In the coordinate ring of `GL₂`, the localized determinant is still `ad - bc`. -/
@[stacks 01KX "rank-two determinant formula"]
theorem localizedDeterminant_eq_ad_sub_bc :
    localizedDeterminant k = localizedA k * localizedD k - localizedB k * localizedC k := sorry

/-- The localized determinant is a unit in the coordinate ring of `GL₂`. -/
@[stacks 01KX "rank-two determinant unit"]
theorem localizedDeterminant_isUnit : IsUnit (localizedDeterminant k) := sorry

/-- The `k`-algebra map `k[x,y] ⟶ k[a,b,c,d,1/(ad-bc)]` sending `x` to `a` and `y` to
`b`. -/
@[stacks 01KX "first-row coordinate comap"]
abbrev toAffinePlaneComap :
    PuncturedAffinePlane.coordinateRing k →ₐ[k] coordinateRing k :=
  GeneralLinear.FirstRow.coordinateComap k 1

/-- The rank-two general linear scheme `GL₂,k`. -/
@[stacks 01KX]
abbrev scheme : Scheme.{u} := GeneralLinear.scheme k (index)

/-- The canonical structure morphism from `GL₂,k` to `Spec(k)`. -/
@[stacks 01KX "rank-two general-linear structure morphism"]
abbrev toBase : scheme k ⟶ Spec (CommRingCat.of k) :=
  GeneralLinear.toBase k (index)

/-- The morphism from `GL₂,k` to canonical affine `2`-space induced by the first matrix row. -/
@[stacks 01KX "first-row morphism to affine two-space"]
abbrev toAffinePlane : scheme k ⟶ PuncturedAffinePlane.affinePlane k :=
  GeneralLinear.FirstRow.toAffineSpace k 1

/-- The comorphism of `toAffinePlane` sends `x` to `a`. -/
@[simp, stacks 01KX "rank-two first-row x-coordinate"]
theorem toAffinePlaneComap_x :
    toAffinePlaneComap k (PuncturedAffinePlane.x k) = localizedA k := sorry

/-- The comorphism of `toAffinePlane` sends `y` to `b`. -/
@[simp, stacks 01KX "rank-two first-row y-coordinate"]
theorem toAffinePlaneComap_y :
    toAffinePlaneComap k (PuncturedAffinePlane.y k) = localizedB k := sorry

/-- The canonical morphism `GL₂,k ⟶ 𝔸²_k ∖ {0}` induced by the first matrix row. -/
@[stacks 01KX "first-row morphism to the punctured affine plane"]
abbrev toPuncturedAffinePlane :
    scheme k ⟶ (PuncturedAffinePlane.puncturedOpen k).toScheme :=
  GeneralLinear.FirstRow.toPuncturedAffineSpace k 1

/-- The punctured-affine morphism composes with the open inclusion to the affine first-row map. -/
@[reassoc (attr := simp), stacks 01KX "rank-two punctured inclusion"]
theorem toPuncturedAffinePlane_ι :
    toPuncturedAffinePlane k ≫ (PuncturedAffinePlane.puncturedOpen k).ι =
      toAffinePlane k := sorry

/-- The canonical morphism from `GL₂,k` to the projective line obtained by projectivizing its
first row. -/
@[stacks 01KX]
abbrev toProjectiveLine : scheme k ⟶ ProjectiveSpace.scheme k 1 :=
  GeneralLinear.FirstRow.toProjectiveSpace k 1

/-- The projectivized first-row morphism is over `Spec(k)`. -/
@[reassoc, stacks 01KX "rank-two projective structure map"]
theorem toProjectiveLine_toBase :
    toProjectiveLine k ≫ ProjectiveSpace.toSpec k 1 = toBase k := sorry

end CommRing

end GLTwo
end
end AlgebraicGeometry

