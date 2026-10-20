/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/- Lemma 65.10.3: let `S` be a scheme, let `U` be a scheme over `S`, and let
`j = (s, t) : R ⟶ U ×_S U` be an étale equivalence relation on `U` over `S`. If the
fppf quotient sheaf `U/R`, namely `P.quotientSheaf (Scheme.fppfTopology.over S)`, has
representable diagonal (the load-bearing algebraic-space condition on `U/R`), then
the canonical map `U ⟶ U/R`, namely `P.quotientMap (Scheme.fppfTopology.over S)`, is
representable, étale, and surjective in the sense of Definition 65.5.1. Hence
`(U, R, U ⟶ U/R)` is a presentation of the algebraic space `U/R`. -/
@[stacks 02WV] #check (AlgebraicGeometry.Scheme.PreRelation.quotientMap_etale_surjective :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (h_representableDiagonal :
      uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj)),
    (MorphismProperty.over (@Etale ⊓ @Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom)

/- The canonical map `U ⟶ U/R` is representable and étale with respect to
`uliftYoneda`. -/
#check (AlgebraicGeometry.Scheme.PreRelation.quotientMap_etale :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (h_representableDiagonal :
      uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj)),
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom)

/- Represented pullbacks of the canonical map `U ⟶ U/R` are surjective morphisms of
schemes over `S`. -/
#check (AlgebraicGeometry.Scheme.PreRelation.quotientMap_surjective :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (h_representableDiagonal :
      uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj)),
    (MorphismProperty.over (@Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom)

/- Under the same hypotheses, the canonical map `U ⟶ U/R` is
étale-locally surjective, and hence with the given étale equivalence relation it is
the atlas of a presentation of the algebraic space `U/R`. -/
#check (AlgebraicGeometry.Scheme.PreRelation.quotientMap_locallySurjective :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (h_representableDiagonal :
      uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj)),
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (P.quotientMap (Scheme.fppfTopology.over S)).hom)

/- The two projections of `P` form the kernel pair of the canonical map `U ⟶ U/R`
in the category of fppf sheaves. This identification does not use representable
diagonal. -/
#check (AlgebraicGeometry.Scheme.PreRelation.isKernelPair_quotientMap :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [IsEquivalenceRelation P.t P.s],
    IsKernelPair (P.quotientMap (Scheme.fppfTopology.over S))
      ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.t)
      ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.s))

/- The data `(U, P, U ⟶ U/R)` satisfies the presentation field list at the
`uliftYoneda`/sheaf layer: the atlas is étale, étale-locally surjective, and has
kernel pair given by the two projections of `P`. -/
#check (AlgebraicGeometry.Scheme.PreRelation.isPresentation_quotientMap :
  ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (h_representableDiagonal :
      uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj)),
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      IsKernelPair (P.quotientMap (Scheme.fppfTopology.over S))
        ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.t)
        ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.s))

end AlgebraicGeometry.Scheme.PreRelation
