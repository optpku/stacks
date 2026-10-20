module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.Affineness
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

/- Lemma 51.16.7 (1): if `A` is an excellent normal local ring and the zero locus
of `I` has dimension at least one, then the local-cohomological dimension of `I`
is strictly less than `ringKrullDim A`. -/
@[stacks 0EB7] #check
  (Ideal.LocalCohomology.dimension_lt_ringKrullDim_of_excellent_normal :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsExcellentRing.{u, u} A]
      [IsNormalRing A] (I : Ideal A) (h_dimension : 1 ≤ ringKrullDim (A ⧸ I)),
      (Ideal.LocalCohomology.dimension I I.fg_of_isNoetherianRing : EInt) <
        WithBot.map (WithTop.map Int.ofNat) (ringKrullDim A))

/- Lemma 51.16.7 (2): if moreover `ringKrullDim A = 2`, then the complement
of the zero locus of `I` in `Spec A` is affine. -/
@[stacks 0EB7] #check
  (Ideal.LocalCohomology.idealComplementOpens_isAffine_of_ringKrullDim_eq_two :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsExcellentRing.{u, u} A]
      [IsNormalRing A] (I : Ideal A) (h_dimension : 1 ≤ ringKrullDim (A ⧸ I))
      (h_ringDimension : ringKrullDim A = 2),
      IsAffineOpen (idealComplementOpens I))
