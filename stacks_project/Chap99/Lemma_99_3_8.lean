module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Representability

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open DerivedCategory.TStructure Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/- Lemma 99.3.8 (1): The degree-zero cohomology-section functor of a pseudo-coherent derived module
is affine and finitely presented when all scheme pullbacks have vanishing degree-minus-one
cohomology. -/
@[stacks 08JX] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.cohomologyZeroFunctor_isAffineFinitePresentation :
    ∀ (K : ModuleDerived B)
    (hK : IsPseudoCoherent B K)
    (hvan : ∀ σ : SchemeOver B,
      IsZero (cohomologySheaf (pullbackOver K σ) (-1))),
      IsAffineFinitePresentationOver (cohomologyZeroFunctor K))

/- Lemma 99.3.8 (2): A pseudo-coherent derived module is perfect when every scheme pullback has
vanishing negative cohomology. -/
@[stacks 08JX] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.isPerfect_of_negativePullbackCohomology :
    ∀ (K : ModuleDerived B)
    (hK : IsPseudoCoherent B K)
    (hvan : ∀ (σ : SchemeOver B) (i : ℤ), i < 0 →
      IsZero (cohomologySheaf (pullbackOver K σ) i)),
      IsPerfect K)

/- Lemma 99.3.8 (3): A pseudo-coherent derived module whose scheme pullbacks have vanishing negative
cohomology has Tor-amplitude in `[0, b]` for some `b ≥ 0` on each affine étale scheme over the base.
-/
@[stacks 08JX] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.exists_hasTorAmplitudeIn_of_negativePullbackCohomology :
    ∀ (K : ModuleDerived B) (hK : IsPseudoCoherent B K)
    (hvan : ∀ (σ : SchemeOver B) (i : ℤ), i < 0 →
      IsZero (cohomologySheaf (pullbackOver K σ) i)),
      ∀ (σ : SchemeOver B) [Etale σ.hom] [AlgebraicGeometry.IsAffine σ.left.left],
      ∃ b : ℤ, 0 ≤ b ∧ HasTorAmplitudeIn (pullbackOver K σ) 0 b)

/- Lemma 99.3.8 (4): The derived degree-zero section functor of a pseudo-coherent derived module is
affine and finitely presented when every scheme pullback has vanishing negative cohomology. -/
@[stacks 08JX] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.derivedZeroFunctor_isAffineFinitePresentation :
    ∀ (K : ModuleDerived B)
    (hK : IsPseudoCoherent B K)
    (hvan : ∀ (σ : SchemeOver B) (i : ℤ), i < 0 →
      IsZero (cohomologySheaf (pullbackOver K σ) i)),
      IsAffineFinitePresentationOver (derivedZeroFunctor K))

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
