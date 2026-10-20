module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Etale

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The fppf quotient sheaf of an étale equivalence relation on a scheme over a base
scheme has representable diagonal. -/
@[stacks 02WW]
theorem quotientSheaf_representableDiagonal {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    uliftYoneda.{u + 1}.relativelyRepresentable
      (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj) := sorry

/-- The canonical map from a scheme to the fppf quotient of an étale equivalence
relation is representable, étale, and surjective. -/
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
