module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Properties

/-!
# Affine spectrum morphisms from subalgebras

This module records inheritance properties of affine spectrum morphisms when
an algebra is replaced by a subalgebra over the same base ring.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace UniversalHomeomorphism

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- If the spectrum morphism of an algebra is a universal homeomorphism, then so is the
spectrum morphism of every subalgebra over the same base ring. -/
theorem specMap_of_subalgebra
    (B' : Subalgebra A B)
    (hf : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B'))) := sorry

/-- If the spectrum morphism of an algebra is a universal homeomorphism inducing isomorphisms
on residue fields, then every subalgebra over the same base has both properties. -/
theorem specMap_of_subalgebra_and_residueFieldMap_isIso
    (B' : Subalgebra A B)
    (hf : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hκ :
      ∀ x : Spec (CommRingCat.of B),
        IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueFieldMap x)) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B'))) ∧
      ∀ x : Spec (CommRingCat.of B'),
        IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B'))).residueFieldMap x) := sorry

end UniversalHomeomorphism

namespace UniversallyClosed

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- If the spectrum morphism of an algebra is universally closed, then so is the spectrum
morphism of every subalgebra over the same base ring. -/
theorem specMap_of_subalgebra
    (B' : Subalgebra A B)
    (hf : UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap A B'))) := sorry

/-- If the spectrum morphism of an algebra is universally closed and universally injective,
then every subalgebra over the same base has both properties. -/
theorem specMap_of_subalgebra_and_universallyInjective
    (B' : Subalgebra A B)
    (hclosed : UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hinj : UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap A B'))) ∧
      UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap A B'))) := sorry

end UniversallyClosed

end AlgebraicGeometry
