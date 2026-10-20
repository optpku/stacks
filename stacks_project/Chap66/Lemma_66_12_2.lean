module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Subspace

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

/- Lemma 66.12.2: invariant locally closed subschemes correspond canonically to locally closed
subspaces of the quotient, with openness and closedness preserved and reflected. -/
@[stacks 07TW] #check (AlgebraicGeometry.Scheme.PreRelation.locallyClosedSubspaceEquiv :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation],
    InvariantImmersion.SubobjectClass P ≃ LocallyClosedSubspace.SubobjectClass P)

#check (AlgebraicGeometry.Scheme.PreRelation.pullbackAlong_toLocallyClosedSubspace_subobject :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z : LocallyClosedSubspace P),
    (Z.pullbackAlong.toLocallyClosedSubspace).subobject = Z.subobject)

#check (AlgebraicGeometry.Scheme.PreRelation.toLocallyClosedSubspace_pullbackAlong_subobject :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z' : InvariantImmersion P),
    (Z'.toLocallyClosedSubspace.pullbackAlong).subobject = Z'.subobject)

#check (AlgebraicGeometry.Scheme.PreRelation.isClosedImmersion_pullbackAlong_iff :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z : LocallyClosedSubspace P),
    (over (@AlgebraicGeometry.IsClosedImmersion)).relative uliftYoneda.{u + 1} Z.ι.hom ↔
      AlgebraicGeometry.IsClosedImmersion Z.pullbackAlong.ι.left)

#check (AlgebraicGeometry.Scheme.PreRelation.isOpenImmersion_pullbackAlong_iff :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z : LocallyClosedSubspace P),
    (over (@AlgebraicGeometry.IsOpenImmersion)).relative uliftYoneda.{u + 1} Z.ι.hom ↔
      AlgebraicGeometry.IsOpenImmersion Z.pullbackAlong.ι.left)
