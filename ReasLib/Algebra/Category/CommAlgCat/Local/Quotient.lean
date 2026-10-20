module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.Algebra.Category.CommAlgCat.Local
public import ReasLib.RingTheory.LocalRing.Quotient

/-!
# Quotients in the category of local algebras

This module provides the quotient object of a local algebra base and its universal map to a
local algebra on which the defining ideal vanishes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace LocalAlgCat

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The canonical structure map from a local ring to a quotient by an ideal below its maximal
ideal is local. -/
theorem quotientAlgebraMapIsLocal (I : Ideal A)
    (hI : I ≤ IsLocalRing.maximalIdeal A) :
    IsLocalHom (algebraMap A (A ⧸ I)) := sorry

/-- The quotient by an ideal below the maximal ideal, as a local algebra over the original
ring. -/
def quotient (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) : LocalAlgCat.{u} A :=
  ⟨⟨CommAlgCat.of A (A ⧸ I), IsLocalRing.quotient_of_le_maximalIdeal I hI,
    quotientAlgebraMapIsLocal A I hI⟩⟩

/-- The carrier of the local-algebra quotient is the ordinary ideal quotient. -/
theorem carrier_quotient (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) :
    carrier A (quotient A I hI) = (A ⧸ I) := sorry

/-- Morphisms from a local-algebra quotient to a fixed local algebra are unique. -/
instance quotientHomSubsingleton (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A)
    (T : LocalAlgCat.{u} A) : Subsingleton (quotient A I hI ⟶ T) := sorry

/-- If the image of an ideal in a local algebra is zero, every element of the ideal maps to
zero. -/
theorem quotientLift_zero (I : Ideal A) (T : LocalAlgCat.{u} A)
    (hmap : I.map (algebraMap A T) = ⊥) (a : A) (ha : a ∈ I) :
    Algebra.ofId A T a = 0 := sorry

/-- The algebra homomorphism induced from a quotient by a vanishing ideal is local. -/
theorem quotientLiftIsLocal (I : Ideal A) (T : LocalAlgCat.{u} A)
    (hmap : I.map (algebraMap A T) = ⊥) :
    IsLocalHom
      (Ideal.Quotient.liftₐ I (Algebra.ofId A T)
        (fun a ha ↦ quotientLift_zero A I T hmap a ha)).toRingHom := sorry

/-- The canonical local-algebra morphism from a quotient to a local algebra annihilating the
defining ideal. -/
def quotientLift (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A)
    (T : LocalAlgCat.{u} A) (hmap : I.map (algebraMap A T) = ⊥) :
    quotient A I hI ⟶ T :=
  ofHom A
    { hom := Ideal.Quotient.liftₐ I (Algebra.ofId A T)
        (fun a ha ↦ quotientLift_zero A I T hmap a ha)
      isLocal := quotientLiftIsLocal A I T hmap }

/-- Composing the quotient lift with the quotient map recovers the structure map of the target
local algebra. -/
theorem quotientLift_comp_mk (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A)
    (T : LocalAlgCat.{u} A) (hmap : I.map (algebraMap A T) = ⊥) :
    (Hom.toLocal A (quotientLift A I hI T hmap)).hom.toRingHom.comp
        (Ideal.Quotient.mk I) = algebraMap A T := sorry

/-- Maps from the local-algebra quotient exist exactly when the target structure map annihilates
the defining ideal. -/
theorem nonempty_hom_quotient_iff (I : Ideal A)
    (hI : I ≤ IsLocalRing.maximalIdeal A) (T : LocalAlgCat.{u} A) :
    Nonempty (quotient A I hI ⟶ T) ↔ I.map (algebraMap A T) = ⊥ := sorry

end LocalAlgCat
