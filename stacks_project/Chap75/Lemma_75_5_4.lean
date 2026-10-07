module

public import stacks_project.Chap75.Lemma_75_5_4_Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/- Lemma 75.5.4 (1): if the transition maps on every cohomology sheaf of a sequential inverse
system in `D_QCoh(𝒪_X)` are epimorphisms, then the cohomology sheaf of a derived limit is
isomorphic to the inverse limit of the cohomology sheaves. -/
@[stacks 0D3E] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.cohomologySheaf_iso_limit_of_epi :
    ∀ (Ksys : SequentialInverseSystem (DerivedQCoh X))
      (K : ModuleDerived X)
      (hK : IsDerivedLimit (Ksys ⋙ inclusion X) K)
      (h_epi : cohomologyTransitionEpi Ksys)
      (q : ℤ),
      IsIsomorphic ((DerivedCategory.homologyFunctor (Modules X) q).obj K)
        (limit (cohomologySystem Ksys q)))

/- Lemma 75.5.4 (2): under the same degreewise epimorphism hypothesis, the ordinary inverse
limit of the degree-`q` cohomology sheaves, placed in degree zero, is a homotopy limit of their
sequential inverse system. -/
@[stacks 0D3E] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.cohomologySheaf_limit_isOf_of_epi :
    ∀ (Ksys : SequentialInverseSystem (DerivedQCoh X))
      (K : ModuleDerived X)
      (hK : IsDerivedLimit (Ksys ⋙ inclusion X) K)
      (h_epi : cohomologyTransitionEpi Ksys)
      (q : ℤ),
      HomotopyLimit.IsOf
        (cohomologySystem Ksys q ⋙ DerivedCategory.singleFunctor (Modules X) (0 : ℤ))
        ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj
          (limit (cohomologySystem Ksys q))))

/- Lemma 75.5.4 (3): under the same hypotheses, the inverse limit of the degree-`q` cohomology
sheaves has vanishing positive cohomology on every affine object of `X_étale`. -/
@[stacks 0D3E] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.cohomologySheaf_limit_higherCohomology_isZero_of_epi :
    ∀ (Ksys : SequentialInverseSystem (DerivedQCoh X))
      (K : ModuleDerived X)
      (hK : IsDerivedLimit (Ksys ⋙ inclusion X) K)
      (h_epi : cohomologyTransitionEpi Ksys)
      (q : ℤ) (U : smallEtaleSite X) [IsAffine U.left.left] (p : ℕ) (hp : 0 < p)
      [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})],
      IsZero
        (Sheaf.H'
          ((SheafOfModules.toSheaf (structureSheaf X)).obj
            (limit (cohomologySystem Ksys q)))
          p U))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

end
