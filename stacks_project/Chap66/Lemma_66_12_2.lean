/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_12_2_Comparison
public import stacks_project.Chap66.Lemma_66_12_2_Invariant

/-!
# Lemma 66.12.2

Canonical bijection between `R`-invariant locally closed subschemes of `U` and locally closed
subspaces of the associated algebraic space `X = U / R`, with closed and open immersions
transported along the correspondence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PreRelation
open MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- Lemma 66.12.2 (1): let `S` be a scheme, let `P` be an étale equivalence relation on a scheme
`U` over `S`, and let `X = P.quotientSheaf (Scheme.fppfTopology.over S)` be the associated fppf
quotient sheaf. Pulling a locally closed subspace `Z ⊂ X` back along the quotient map and
quotienting the restricted relation recovers `Z` as a subobject. -/
@[stacks 07TW]
theorem pullbackAlong_toLocallyClosedSubspace_subobject {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z : LocallyClosedSubspace P) :
    (Z.pullbackAlong.toLocallyClosedSubspace).subobject = Z.subobject := sorry

/-- Lemma 66.12.2 (2): let `S` be a scheme, let `P` be an étale equivalence relation on a scheme
`U` over `S`, and let `X = P.quotientSheaf (Scheme.fppfTopology.over S)` be the associated fppf
quotient sheaf. Quotienting an `R`-invariant locally closed subscheme `Z' ⊂ U` and pulling the
resulting subspace back along the quotient map recovers `Z'` as a subobject. -/
@[stacks 07TW]
theorem toLocallyClosedSubspace_pullbackAlong_subobject {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z' : InvariantImmersion P) :
    (Z'.toLocallyClosedSubspace.pullbackAlong).subobject = Z'.subobject := sorry

/-- Lemma 66.12.2 (3): under the correspondence of Lemma 66.12.2, `Z ⟶ X` is a closed immersion
if and only if the corresponding `Z' ⟶ U` is a closed immersion. -/
@[stacks 07TW]
theorem isClosedImmersion_pullbackAlong_iff {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z : LocallyClosedSubspace P) :
    (over (@AlgebraicGeometry.IsClosedImmersion)).relative uliftYoneda.{u + 1} Z.ι.hom ↔
      AlgebraicGeometry.IsClosedImmersion Z.pullbackAlong.ι.left := sorry

/-- Lemma 66.12.2 (4): under the correspondence of Lemma 66.12.2, `Z ⟶ X` is an open immersion
if and only if the corresponding `Z' ⟶ U` is an open immersion. -/
@[stacks 07TW]
theorem isOpenImmersion_pullbackAlong_iff {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z : LocallyClosedSubspace P) :
    (over (@AlgebraicGeometry.IsOpenImmersion)).relative uliftYoneda.{u + 1} Z.ι.hom ↔
      AlgebraicGeometry.IsOpenImmersion Z.pullbackAlong.ι.left := sorry

end AlgebraicGeometry.Scheme.PreRelation
