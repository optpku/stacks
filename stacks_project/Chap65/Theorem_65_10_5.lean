module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Presentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/- Theorem 65.10.5: let `S` be a scheme, let `U` be a scheme over `S`, and let
`j = (s, t) : R ⟶ U ×_S U` be an étale equivalence relation on `U` over `S`. Then the
fppf quotient sheaf `U/R` is an algebraic space, and the canonical map `U ⟶ U/R`
is étale and surjective, giving a presentation of `U/R`. -/
@[stacks 02WW] #check (AlgebraicGeometry.Scheme.PreRelation.quotientSheaf_spec :
    ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation],
    uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj) ∧
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        (P.quotientMap (Scheme.fppfTopology.over S)).hom)

/- The fppf quotient sheaf `U/R` has representable diagonal. -/
#check (AlgebraicGeometry.Scheme.PreRelation.quotientSheaf_representableDiagonal :
    ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation],
    uliftYoneda.{u + 1}.relativelyRepresentable
      (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj))

/- The canonical map `U ⟶ U/R` is étale and surjective in the sense of
Definition 65.5.1. -/
#check (AlgebraicGeometry.Scheme.PreRelation.etale_surjective_quotientMap :
    ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation],
    (MorphismProperty.over (@Etale ⊓ @Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom)

/- The canonical map `U ⟶ U/R` is relatively representable with respect to
`uliftYoneda`. -/
#check (AlgebraicGeometry.Scheme.PreRelation.quotientMap_relativelyRepresentable :
    ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation],
    uliftYoneda.{u + 1}.relativelyRepresentable
      (P.quotientMap (Scheme.fppfTopology.over S)).hom)

/- The canonical map `U ⟶ U/R` is representable and étale with respect to
`uliftYoneda`. -/
#check (AlgebraicGeometry.Scheme.PreRelation.etale_quotientMap :
    ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation],
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom)

/- Represented pullbacks of the canonical map `U ⟶ U/R` are surjective morphisms of
schemes over `S`. -/
#check (AlgebraicGeometry.Scheme.PreRelation.surjective_quotientMap :
    ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation],
    (MorphismProperty.over (@Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom)

/- The canonical map `U ⟶ U/R` is étale-locally surjective. -/
#check (AlgebraicGeometry.Scheme.PreRelation.locallySurjective_quotientMap :
    ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation],
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (P.quotientMap (Scheme.fppfTopology.over S)).hom)

/- The data `(U, P, U ⟶ U/R)` is a presentation of `U/R` at the `uliftYoneda`/sheaf
layer: `P` is an étale equivalence relation, the atlas is étale and étale-locally
surjective, and the two projections of `P` form the kernel pair of the atlas. -/
#check (AlgebraicGeometry.Scheme.PreRelation.isPresentation_quotientSheaf :
    ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation],
    P.IsEtaleEquivalenceRelation ∧
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      IsKernelPair (P.quotientMap (Scheme.fppfTopology.over S))
        ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.t)
        ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.s))

end AlgebraicGeometry.Scheme.PreRelation
