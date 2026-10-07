module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import stacks_project.Chap65.Definition_65_9_3_EtaleEquivalence

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- Lemma 65.10.4 (1): let `S` be a scheme, let `U` be an affine scheme over `S`, and let
`j = (s, t) : R ⟶ U ×_S U` be an étale equivalence relation on `U` over `S`. Then the
fppf quotient sheaf `U/R`, namely `P.quotientSheaf (Scheme.fppfTopology.over S)`, has
representable diagonal. -/
@[stacks 0265]
theorem quotientSheaf_representableDiagonal_of_isAffine {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] [IsAffine U.left] :
    uliftYoneda.{u + 1}.relativelyRepresentable
      (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj) := sorry

/-- Lemma 65.10.4 (2): under the same hypotheses, the canonical map `U ⟶ U/R`, namely
`P.quotientMap (Scheme.fppfTopology.over S)`, is étale and surjective in the sense of
Definition 65.5.1. -/
@[stacks 0265]
theorem quotientMap_etale_surjective_of_isAffine {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] [IsAffine U.left] :
    (MorphismProperty.over (@Etale ⊓ @Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The canonical map `U ⟶ U/R` is relatively representable with respect to
`uliftYoneda`. -/
theorem quotientMap_relativelyRepresentable_of_isAffine {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] [IsAffine U.left] :
    uliftYoneda.{u + 1}.relativelyRepresentable
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The canonical map `U ⟶ U/R` is representable and étale with respect to
`uliftYoneda`. -/
theorem quotientMap_etale_of_isAffine {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] [IsAffine U.left] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- Represented pullbacks of the canonical map `U ⟶ U/R` are surjective morphisms of
schemes over `S`. -/
theorem quotientMap_surjective_of_isAffine {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] [IsAffine U.left] :
    (MorphismProperty.over (@Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The canonical map `U ⟶ U/R` is étale-locally surjective. -/
theorem quotientMap_locallySurjective_of_isAffine {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] [IsAffine U.left] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The fppf quotient sheaf `U/R` of an étale equivalence relation on an affine scheme
over `S` is an algebraic space at the sheaf layer: it has representable diagonal, and
the canonical atlas `U ⟶ U/R` is representable étale and étale-locally surjective. -/
theorem quotientSheaf_spec_of_isAffine {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] [IsAffine U.left] :
    uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj) ∧
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

end AlgebraicGeometry.Scheme.PreRelation
