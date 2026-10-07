module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
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

/-- Theorem 65.10.5 (1): let `S` be a scheme, let `U` be a scheme over `S`, and let
`j = (s, t) : R ⟶ U ×_S U` be an étale equivalence relation on `U` over `S`. Then the
fppf quotient sheaf `U/R`, namely `P.quotientSheaf (Scheme.fppfTopology.over S)`, has
representable diagonal. -/
@[stacks 02WW]
theorem quotientSheaf_representableDiagonal {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    uliftYoneda.{u + 1}.relativelyRepresentable
      (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj) := sorry

/-- Theorem 65.10.5 (2): under the same hypotheses, the canonical map `U ⟶ U/R`, namely
`P.quotientMap (Scheme.fppfTopology.over S)`, is étale and surjective in the sense of
Definition 65.5.1. -/
@[stacks 02WW]
theorem etale_surjective_quotientMap {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    (MorphismProperty.over (@Etale ⊓ @Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The canonical map `U ⟶ U/R` is relatively representable with respect to
`uliftYoneda`. -/
theorem quotientMap_relativelyRepresentable {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    uliftYoneda.{u + 1}.relativelyRepresentable
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The canonical map `U ⟶ U/R` is representable and étale with respect to
`uliftYoneda`. -/
theorem etale_quotientMap {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- Represented pullbacks of the canonical map `U ⟶ U/R` are surjective morphisms of
schemes over `S`. -/
theorem surjective_quotientMap {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    (MorphismProperty.over (@Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The canonical map `U ⟶ U/R` is étale-locally surjective. -/
theorem locallySurjective_quotientMap {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The fppf quotient sheaf `U/R` of an étale equivalence relation on a scheme over `S`
is an algebraic space at the sheaf layer: it has representable diagonal, and the
canonical atlas `U ⟶ U/R` is representable étale and étale-locally surjective. -/
theorem quotientSheaf_spec {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj) ∧
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The data `(U, P, U ⟶ U/R)` is a presentation of `U/R` at the `uliftYoneda`/sheaf
layer: `P` is an étale equivalence relation, the atlas is étale and étale-locally
surjective, and the two projections of `P` form the kernel pair of the atlas. -/
theorem isPresentation_quotientSheaf {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    P.IsEtaleEquivalenceRelation ∧
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      IsKernelPair (P.quotientMap (Scheme.fppfTopology.over S))
        ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.t)
        ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.s) := sorry

end AlgebraicGeometry.Scheme.PreRelation
