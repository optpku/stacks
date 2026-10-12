/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Quotients of ring homomorphisms

This file owns the map induced on quotients by extending an ideal from the
source.  It is map-first and does not require an ambient `Algebra` instance.
-/

universe u v

namespace RingHom

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- The ring homomorphism induced by `f` after quotienting by a source ideal
and its image in the target. -/
@[stacks 07CM "quotient map by a source ideal"]
def quotientByIdeal (f : R →+* A) (I : Ideal R) :
    R ⧸ I →+* A ⧸ I.map f :=
  Ideal.quotientMap (I.map f) f Ideal.le_comap_map

/-- The homomorphism induced by `f` on quotients by compatible source and
target ideals. Compatibility is stated map-first as `I.map f ≤ J`. -/
@[stacks 09PX "quotient map by compatible ideals"]
def quotientByIdeals (f : R →+* A) (I : Ideal R) (J : Ideal A)
    (hIJ : I.map f ≤ J) : R ⧸ I →+* A ⧸ J :=
  Ideal.quotientMap J f (Ideal.map_le_iff_le_comap.mp hIJ)

/-- If the composite `R → A → A ⧸ J` is surjective, then its canonical
comparison from the quotient by `J.comap f` is bijective.  This is the
map-first first stage of an ideal-power quotient tower. -/
@[stacks 0H1D "surjective quotient comparison"]
theorem quotientMap_bijective_of_surjective
    (f : R →+* A) (J : Ideal A)
    (h_surjective : Function.Surjective ((Ideal.Quotient.mk J).comp f)) :
    Function.Bijective
      ((Ideal.quotientMap J f le_rfl) : R ⧸ (Ideal.comap f J) →+* A ⧸ J) := sorry

/-- The quotient of a ring homomorphism sends a residue class to the residue
class of its image. -/
@[simp]
theorem quotientByIdeal_mk (f : R →+* A) (I : Ideal R) (x : R) :
    f.quotientByIdeal I (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk (I.map f) (f x) := sorry

/-- A quotient map by compatible ideals sends the class of `x` to the class
of `f x`. -/
@[simp]
theorem quotientByIdeals_mk (f : R →+* A) (I : Ideal R) (J : Ideal A)
    (hIJ : I.map f ≤ J) (x : R) :
    f.quotientByIdeals I J hIJ (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk J (f x) := sorry

/-- Quotienting a ring homomorphism commutes with the canonical quotient maps. -/
theorem quotientByIdeal_comp_mk (f : R →+* A) (I : Ideal R) :
    (f.quotientByIdeal I).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map f)).comp f := sorry

end RingHom
