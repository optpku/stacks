module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.Algebra.Category.ModuleCat.Flat.Exact
public import ReasLib.CategoryTheory.Functor.Exactness.ReflectsEpiMono

/-!
# Faithfully flat extension of scalars

Faithful flatness is characterized by exact and faithful extension of scalars. Such extension of
scalars also reflects zero objects, monomorphisms, and epimorphisms.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace ModuleCat.ExtendScalars

/-- Extension of scalars along a faithfully flat homomorphism of commutative rings is exact. -/
theorem exact_of_faithfullyFlat {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat) :
    exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S)
      (ModuleCat.extendScalars.{u, u, u} f) := sorry

/-- Extension of scalars along a faithfully flat homomorphism reflects zero objects. -/
theorem kernel_le_isZero_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.FaithfullyFlat) :
    (ModuleCat.extendScalars.{u, u, u} f).kernel ≤ IsZero := sorry

/-- Extension of scalars along a faithfully flat homomorphism reflects monomorphisms. -/
theorem reflectsMonomorphisms_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.FaithfullyFlat) :
    (ModuleCat.extendScalars.{u, u, u} f).ReflectsMonomorphisms := sorry

/-- Extension of scalars along a faithfully flat homomorphism reflects epimorphisms. -/
theorem reflectsEpimorphisms_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.FaithfullyFlat) :
    (ModuleCat.extendScalars.{u, u, u} f).ReflectsEpimorphisms := sorry

/-- A homomorphism of commutative rings is faithfully flat exactly when extension of scalars is
exact and faithful. -/
theorem faithfullyFlat_iff_exact_and_faithful
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.FaithfullyFlat ↔
      exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S)
          (ModuleCat.extendScalars.{u, u, u} f) ∧
        (ModuleCat.extendScalars.{u, u, u} f).Faithful := sorry

end ModuleCat.ExtendScalars
