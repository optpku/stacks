/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Example_65_14_2_Presentation
public import stacks_project.Chap65.Example_65_14_2_Space
public import stacks_project.Chap65.Example_65_14_2_Descent
public import stacks_project.Chap66.Lemma_66_16_4_Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

universe u

/- The relation `R = Δ(U) ⨿ Δ'(U \ {0_U})` is an étale equivalence relation on
`U = Spec(k'[x])` over `S = Spec(k[x])`. -/
@[stacks 03FN]
#check
  (instIsEtaleEquivalenceRelation_preRelation :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
      (hdeg : Module.finrank k k' = 2),
      (preRelation k k' hdeg).IsEtaleEquivalenceRelation)

/- The quotient `X = U / R` is the fppf sheaf of the étale equivalence
relation, an algebraic space over `S` by Theorem 65.10.5. -/
@[stacks 03FN]
#check sheafOfPoints
@[stacks 03FN]
#check sheafOfPoints_spec
@[stacks 03FN]
#check atlas
@[stacks 03FN]
#check atlas_etale

/- Example 65.14.2 (1): `X → S` is an isomorphism over `S \ {0_S}`. -/
@[stacks 03FN]
#check isIso_over_punctured

/- Example 65.14.2 (2): the morphism `X → S` is étale
(see Properties of Spaces, Definition 66.16.2). -/
@[stacks 03FN]
#check etale_structureHom
@[stacks 03FN]
#check AlgebraicGeometry.AlgebraicSpace.Etale

/- Example 65.14.2 (3): the fibre of `X → S` over `0_S` is isomorphic to `Spec(k') = 0_U`. -/
@[stacks 03FN]
#check fiber_origin_iso

/- Example 65.14.2 (4): `X` is not a scheme. -/
@[stacks 03FN]
#check not_isRepresentable
@[stacks 03FN]
#check impossible_origin_localRing

/- Example 65.14.2 (5): `X` is not separated, but it is locally separated and quasi-separated. -/
@[stacks 03FN]
#check not_isClosedImmersion_diag
@[stacks 03FN]
#check isImmersion_diag
@[stacks 03FN]
#check quasiCompact_diag

/- Example 65.14.2 (6): there is a surjective finite étale morphism `S' → S` such that the
base change `X' = S' ×_S X` is a scheme, namely the affine line with `0` doubled. -/
@[stacks 03FN]
#check etale_cover_hom
@[stacks 03FN]
#check isFinite_cover_hom
@[stacks 03FN]
#check surjective_cover_hom
@[stacks 03FN]
#check iso_doubledOrigin
@[stacks 03FN]
#check DoubledOrigin.scheme

/- Example 65.14.2 (7): viewing `X` over `Spec(k)`, the base change `X_{k'}` is a scheme
but `X` is not a scheme. -/
@[stacks 03FN]
#check scalarExtension_isRepresentable
@[stacks 03FN]
#check not_isRepresentable_overGround

/- Example 65.14.2 (8): this gives a descent datum for schemes relative to
`{Spec(k') → Spec(k)}` which is not effective. -/
@[stacks 03FN]
#check descentData
@[stacks 03FN]
#check not_isEffective_descentData
@[stacks 03FN]
#check Scheme.DescentData.isEffective_iff
@[stacks 03FN]
#check descentObject
@[stacks 03FN]
#check etale_groundCover
