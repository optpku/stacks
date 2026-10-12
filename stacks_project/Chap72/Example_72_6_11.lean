/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap72.Example_72_6_11_ClassGroup
public import stacks_project.Chap72.Example_72_6_11_Relation
public import stacks_project.Chap72.Example_72_6_11_Space
import StacksCheckRecall

/-!
# Example 72.6.11

The quotient of the coordinate axes `U = Spec(k[x, y] / (xy))` by the étale
equivalence relation `R = Δ(U) ⨿ Δ'(U \ {0_U})` is an integral Noetherian
algebraic space `X` with a universal homeomorphism `X ⟶ 𝔸¹_k` that is an
isomorphism off `0`, class group `ℤ/2ℤ`, and henselian local ring at the unique
closed point over `0` which is not a domain.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.AlgebraicSpace.CoordinateAxesQuotient

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoordinateAxesQuotient

/- Example 72.6.11 (1): the relation `R = Δ(U) ⨿ Δ'(U \ {0_U})` is an étale
equivalence relation on `U`. -/
@[stacks 0ENU]
#check
  (instIsEtaleEquivalenceRelation_preRelation :
    ∀ (k : Type u) [Field k], (preRelation k).IsEtaleEquivalenceRelation)

/- Example 72.6.11 (2): the quotient `X = U / R` is an algebraic space. -/
@[stacks 0ENU]
#check sheafOfPoints_spec

/- Example 72.6.11 (3): the morphism `U ⟶ 𝔸¹_k`, `(x, y) ↦ x + y`, is
`R`-invariant and hence defines a morphism `X ⟶ 𝔸¹_k`. -/
@[stacks 0ENU]
#check toAffineLine
@[stacks 0ENU]
#check sumOver_equalizes

/- Example 72.6.11 (4): the morphism `X ⟶ 𝔸¹_k` is a universal homeomorphism. -/
@[stacks 0ENU]
#check universalHomeomorphism_toAffineLine

/- Example 72.6.11 (5): the morphism `X ⟶ 𝔸¹_k` is an isomorphism over
`𝔸¹_k \ {0}`. -/
@[stacks 0ENU]
#check isIso_over_punctured

/-- Example 72.6.11 (6): `X` is integral in the sense of Definition 72.4.1: it is
reduced, decent, and `|X|` is irreducible. The étale atlas `U` is a reduced
scheme, `toAffineLine` is a universal homeomorphism onto the integral scheme
`𝔸¹_k` so `|X|` is irreducible, and the quasi-compact diagonal of `X` is the
QS/decent witness. -/
@[stacks 0ENU]
theorem isIntegral (k : Type u) [Field k] :
    AlgebraicGeometry.IsReduced (cover k).left ∧
      AffineLineInvolution.isUniversalHomeomorphism (toAffineLine k) ∧
      AlgebraicGeometry.IsIntegral (affineLine k).left ∧
      (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k).obj) :=
  sorry

/-- Example 72.6.11 (7): `X` is Noetherian. In this sheaf encoding that means the
étale atlas `U` is a Noetherian scheme and the diagonal of `X` is representably
quasi-compact. -/
@[stacks 0ENU]
theorem isNoetherian (k : Type u) [Field k] :
    AlgebraicGeometry.IsNoetherian (cover k).left ∧
      (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k).obj) :=
  sorry

/- Example 72.6.11 (8): there is a unique closed point `x ∈ |X|` lying over
`0 ∈ 𝔸¹_k`. -/
@[stacks 0ENU]
#check unique_point_over_origin

/- Example 72.6.11 (9): `Cl(X) = ℤ/2ℤ` with generator corresponding to the unique
closed point over `0`. -/
@[stacks 0ENU]
#check classGroupEquivZMod
@[stacks 0ENU]
#check classGroupEquivZMod_origin

/- Example 72.6.11 (10): the henselian local ring of `X` at that point is a
henselization of `originStalk k`, the stalk of `U` at the origin. -/
@[stacks 0ENU]
#check isHenselianLocalRingAtOrigin_of_isHenselizationOf

/- Example 72.6.11 (11): that henselization is not a domain. -/
@[stacks 0ENU]
#check not_isDomain_of_isHenselizationOf_originStalk

end AlgebraicGeometry.AlgebraicSpace.CoordinateAxesQuotient
