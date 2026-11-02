/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
    IsLocalHom (algebraMap A (A ⧸ I)) := by
  letI := IsLocalRing.quotient_of_le_maximalIdeal I hI
  exact IsLocalHom.of_surjective (algebraMap A (A ⧸ I)) Ideal.Quotient.mk_surjective

/-- The quotient by an ideal below the maximal ideal, as a local algebra over the original
ring. -/
def quotient (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) : LocalAlgCat.{u} A :=
  ⟨⟨CommAlgCat.of A (A ⧸ I), IsLocalRing.quotient_of_le_maximalIdeal I hI,
    quotientAlgebraMapIsLocal A I hI⟩⟩

/-- The carrier of the local-algebra quotient is the ordinary ideal quotient. -/
theorem carrier_quotient (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) :
    carrier A (quotient A I hI) = (A ⧸ I) := rfl

/-- Morphisms from a local-algebra quotient to a fixed local algebra are unique. -/
instance quotientHomSubsingleton (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A)
    (T : LocalAlgCat.{u} A) : Subsingleton (quotient A I hI ⟶ T) := by
  refine ⟨fun f g ↦ ?_⟩
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply Ideal.Quotient.algHom_ext
  exact Subsingleton.elim _ _

/-- If the image of an ideal in a local algebra is zero, every element of the ideal maps to
zero. -/
theorem quotientLift_zero (I : Ideal A) (T : LocalAlgCat.{u} A)
    (hmap : I.map (algebraMap A T) = ⊥) (a : A) (ha : a ∈ I) :
    Algebra.ofId A T a = 0 := by
  change algebraMap A T a = 0
  have h := Ideal.mem_map_of_mem (algebraMap A T) ha
  simpa only [hmap, Ideal.mem_bot] using h

/-- The algebra homomorphism induced from a quotient by a vanishing ideal is local. -/
theorem quotientLiftIsLocal (I : Ideal A) (T : LocalAlgCat.{u} A)
    (hmap : I.map (algebraMap A T) = ⊥) :
    IsLocalHom
      (Ideal.Quotient.liftₐ I (Algebra.ofId A T)
        (fun a ha ↦ quotientLift_zero A I T hmap a ha)).toRingHom := by
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply (Ideal.Quotient.mk I).isUnit_map
  exact isUnit_of_map_unit (algebraMap A T) a hx

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
        (Ideal.Quotient.mk I) = algebraMap A T := rfl

/-- Maps from the local-algebra quotient exist exactly when the target structure map annihilates
the defining ideal. -/
theorem nonempty_hom_quotient_iff (I : Ideal A)
    (hI : I ≤ IsLocalRing.maximalIdeal A) (T : LocalAlgCat.{u} A) :
    Nonempty (quotient A I hI ⟶ T) ↔ I.map (algebraMap A T) = ⊥ := by
  constructor
  · rintro ⟨f⟩
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    change algebraMap A T a = 0
    let g : A ⧸ I →ₐ[A] T := (Hom.toLocal A f).hom
    rw [← g.commutes a]
    change g (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · intro hmap
    exact ⟨quotientLift A I hI T hmap⟩

end LocalAlgCat
