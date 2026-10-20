module

public import ReasLib.RingTheory.CotangentComplex.Functoriality
public import ReasLib.Algebra.CharP.Frobenius
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.FieldTheory.Perfect

/-!
# Frobenius maps of cotangent complexes

The Frobenius square of a ring homomorphism induces a canonical map on its
standard cotangent complex.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

universe u

noncomputable section

namespace Algebra.CotangentComplex.Frobenius

/-- The map on a cotangent complex induced by the Frobenius square. -/
def map (p : ℕ) [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hp : (p : A) = 0) :
    ((ModuleCat.extendScalars
        (RingHom.frobeniusOfPrime p (RingHom.natCast_eq_zero_of_eq_zero p f hp))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (RingHom.cotangentComplex f) ⟶
    RingHom.cotangentComplex f :=
  Algebra.CotangentComplex.map f f (RingHom.frobeniusOfPrime p hp)
    (RingHom.frobeniusOfPrime p (RingHom.natCast_eq_zero_of_eq_zero p f hp))
    (RingHom.frobeniusOfPrime_naturality p f hp
      (RingHom.natCast_eq_zero_of_eq_zero p f hp))

/-- The Frobenius cotangent map unfolds to the functoriality map of its square. -/
theorem map_eq (p : ℕ) [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hp : (p : A) = 0) :
    map p f hp =
      Algebra.CotangentComplex.map f f (RingHom.frobeniusOfPrime p hp)
        (RingHom.frobeniusOfPrime p (RingHom.natCast_eq_zero_of_eq_zero p f hp))
        (RingHom.frobeniusOfPrime_naturality p f hp
          (RingHom.natCast_eq_zero_of_eq_zero p f hp)) :=
  rfl

/-- The Frobenius-induced endomorphism of a cotangent complex is null-homotopic
when the characteristic prime vanishes in the source ring. -/
theorem map_homotopic_zero (p : ℕ) [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hp : (p : A) = 0) :
    Nonempty (Homotopy (map p f hp) 0) :=
  sorry

/-- The cotangent complex of a homomorphism between perfect rings vanishes in the
derived category when the characteristic prime vanishes in the source ring. -/
theorem cotangentComplex_isZero (p : ℕ) [Fact p.Prime] {A B : Type u}
    [CommRing A] [CommRing B] (f : A →+* B) (hp : (p : A) = 0)
    [PerfectRing A p] [PerfectRing B p] :
    IsZero (DerivedCategory.Q.obj (RingHom.cotangentComplex f)) :=
  sorry

/-- The André-Quillen cotangent complex of a perfect algebra over a perfect ring
vanishes in the derived category when `p = 0` in the base. -/
theorem derived_isZero (p : ℕ) [Fact p.Prime] (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] (hp : (p : A) = 0)
    [PerfectRing A p] [PerfectRing B p] :
    IsZero (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) :=
  cotangentComplex_isZero p (algebraMap A B) hp

end Algebra.CotangentComplex.Frobenius

