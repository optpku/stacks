module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Cotangent maps of local algebra homomorphisms

A local algebra homomorphism induces a linear map on the cotangent spaces of
the maximal ideals.
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace IsLocalRing.CotangentSpace

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable [Algebra R A] [Algebra R B]

/-- The map of cotangent spaces induced by a local algebra homomorphism. -/
def mapAlgHom (f : A →ₐ[R] B) [IsLocalHom f] :
    CotangentSpace A →ₗ[R] CotangentSpace B :=
  Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) f
    (maximalIdeal_comap (f : A →+* B)).symm.le

/-- The induced cotangent map sends the class of an element of the maximal ideal to the
class of its image. -/
@[simp]
theorem mapAlgHom_toCotangent (f : A →ₐ[R] B) [IsLocalHom f] (x : maximalIdeal A) :
    mapAlgHom f ((maximalIdeal A).toCotangent x) =
      (maximalIdeal B).toCotangent ⟨f x, (maximalIdeal_comap (f : A →+* B)).symm.le x.2⟩ :=
  rfl

end IsLocalRing.CotangentSpace
