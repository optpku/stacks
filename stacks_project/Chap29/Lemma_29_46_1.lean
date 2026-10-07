module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Subalgebra

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.46.1 (1): universal homeomorphisms of affine spectra pass to subalgebras. -/
@[stacks 0CN7]
#check
  (AlgebraicGeometry.UniversalHomeomorphism.specMap_of_subalgebra :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (B' : Subalgebra A B),
      UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))) →
        UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B'))))

/- Lemma 29.46.1 (2): universal homeomorphisms inducing residue-field isomorphisms pass to
subalgebras. -/
@[stacks 0CN7]
#check
  (AlgebraicGeometry.UniversalHomeomorphism.specMap_of_subalgebra_and_residueFieldMap_isIso :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (B' : Subalgebra A B),
      UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))) →
        (∀ x : Spec (CommRingCat.of B),
          IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueFieldMap x)) →
          UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B'))) ∧
            ∀ x : Spec (CommRingCat.of B'),
              IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B'))).residueFieldMap x))

/- Lemma 29.46.1 (3): universally closed affine spectrum morphisms pass to subalgebras. -/
@[stacks 0CN7]
#check
  (AlgebraicGeometry.UniversallyClosed.specMap_of_subalgebra :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (B' : Subalgebra A B),
      UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap A B))) →
        UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap A B'))))

/- Lemma 29.46.1 (4): universally closed and universally injective affine spectrum morphisms pass
to subalgebras. -/
@[stacks 0CN7]
#check
  (AlgebraicGeometry.UniversallyClosed.specMap_of_subalgebra_and_universallyInjective :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (B' : Subalgebra A B),
      UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap A B))) →
        UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap A B))) →
          UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap A B'))) ∧
            UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap A B'))))
