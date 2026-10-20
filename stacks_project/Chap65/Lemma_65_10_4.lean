/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Affine
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/- Lemma 65.10.4: the fppf quotient of an étale equivalence relation on an affine
scheme over `S` is an algebraic space, and its canonical quotient map is étale and
surjective. -/
@[stacks 0265] #check (AlgebraicGeometry.Scheme.PreRelation.quotientSheaf_spec_of_isAffine :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U),
    [P.IsEtaleEquivalenceRelation] → [IsAffine U.left] →
    uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj) ∧
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        (P.quotientMap (Scheme.fppfTopology.over S)).hom)

#check (AlgebraicGeometry.Scheme.PreRelation.quotientSheaf_representableDiagonal_of_isAffine :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U),
    [P.IsEtaleEquivalenceRelation] → [IsAffine U.left] →
    uliftYoneda.{u + 1}.relativelyRepresentable
      (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj))

#check (AlgebraicGeometry.Scheme.PreRelation.quotientMap_etale_surjective_of_isAffine :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U),
    [P.IsEtaleEquivalenceRelation] → [IsAffine U.left] →
    (MorphismProperty.over (@Etale ⊓ @Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom)

#check (AlgebraicGeometry.Scheme.PreRelation.quotientMap_relativelyRepresentable_of_isAffine :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U),
    [P.IsEtaleEquivalenceRelation] → [IsAffine U.left] →
    uliftYoneda.{u + 1}.relativelyRepresentable
      (P.quotientMap (Scheme.fppfTopology.over S)).hom)

#check (AlgebraicGeometry.Scheme.PreRelation.quotientMap_etale_of_isAffine :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U),
    [P.IsEtaleEquivalenceRelation] → [IsAffine U.left] →
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom)

#check (AlgebraicGeometry.Scheme.PreRelation.quotientMap_surjective_of_isAffine :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U),
    [P.IsEtaleEquivalenceRelation] → [IsAffine U.left] →
    (MorphismProperty.over (@Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom)

#check (AlgebraicGeometry.Scheme.PreRelation.quotientMap_locallySurjective_of_isAffine :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U),
    [P.IsEtaleEquivalenceRelation] → [IsAffine U.left] →
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (P.quotientMap (Scheme.fppfTopology.over S)).hom)

end AlgebraicGeometry.Scheme.PreRelation
