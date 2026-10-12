/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AffinePlane.BlowupInverseImage
import StacksCheckRecall

/-!
# Inverse images under the origin blowup of the affine plane

The scheme-theoretic inverse image of `V(X 0 ^ 3, X 0 ^ 2 * X 1, X 0 * X 1 ^ 2, X 1 ^ 3)`
under the blowup of `A²_k` at the origin is an effective Cartier divisor, while an
explicit intermediate ideal provides a counterexample.
-/

@[expose] public section

universe u

open AlgebraicGeometry
open scoped AlgebraicGeometry

/- Exercise 111.61.5: the cubic monomial ideal has Cartier inverse image under
the origin blowup of the affine plane. -/
@[stacks 0ELK]
#check
  (AlgebraicGeometry.AffinePlaneBlowup.cubicIdealSheaf_comap_hom_isEffectiveCartierDivisor :
    ∀ (k : Type u) [Field k],
      IsEffectiveCartierDivisor
        ((AlgebraicGeometry.AffinePlaneBlowup.cubicIdealSheaf k).comap
          (AlgebraicGeometry.AffinePlaneBlowup.hom k)).subschemeι)

/- Exercise 111.61.5: the intermediate ideal gives a non-Cartier inverse image. -/
@[stacks 0ELK]
#check
  (AlgebraicGeometry.AffinePlaneBlowup.nonCartierIdealSheaf_comap_hom_not_isEffectiveCartierDivisor :
    ∀ (k : Type u) [Field k],
      ¬ IsEffectiveCartierDivisor
        ((AlgebraicGeometry.AffinePlaneBlowup.nonCartierIdealSheaf k).comap
          (AlgebraicGeometry.AffinePlaneBlowup.hom k)).subschemeι)

#check (AlgebraicGeometry.AffinePlaneBlowup.cubicIdeal :
  ∀ (k : Type u) [Field k], Ideal (AlgebraicGeometry.AffinePlaneBlowup.coordinateRing k))
#check (AlgebraicGeometry.AffinePlaneBlowup.cubicIdeal_eq_pow :
  ∀ (k : Type u) [Field k],
    AlgebraicGeometry.AffinePlaneBlowup.cubicIdeal k =
      AlgebraicGeometry.AffinePlaneBlowup.originIdeal k ^ 3)
#check (AlgebraicGeometry.AffinePlaneBlowup.cubicIdeal_le_originIdeal :
  ∀ (k : Type u) [Field k],
    AlgebraicGeometry.AffinePlaneBlowup.cubicIdeal k ≤
      AlgebraicGeometry.AffinePlaneBlowup.originIdeal k)
#check (AlgebraicGeometry.AffinePlaneBlowup.cubicIdealSheaf :
  ∀ (k : Type u) [Field k],
    (AlgebraicGeometry.AffinePlaneBlowup.affinePlane k).IdealSheafData)
#check (AlgebraicGeometry.AffinePlaneBlowup.nonCartierIdeal :
  ∀ (k : Type u) [Field k], Ideal (AlgebraicGeometry.AffinePlaneBlowup.coordinateRing k))
#check (AlgebraicGeometry.AffinePlaneBlowup.cubicIdeal_le_nonCartierIdeal :
  ∀ (k : Type u) [Field k],
    AlgebraicGeometry.AffinePlaneBlowup.cubicIdeal k ≤
      AlgebraicGeometry.AffinePlaneBlowup.nonCartierIdeal k)
#check (AlgebraicGeometry.AffinePlaneBlowup.nonCartierIdeal_le_originIdeal :
  ∀ (k : Type u) [Field k],
    AlgebraicGeometry.AffinePlaneBlowup.nonCartierIdeal k ≤
      AlgebraicGeometry.AffinePlaneBlowup.originIdeal k)
#check (AlgebraicGeometry.AffinePlaneBlowup.nonCartierIdealSheaf :
  ∀ (k : Type u) [Field k],
    (AlgebraicGeometry.AffinePlaneBlowup.affinePlane k).IdealSheafData)
