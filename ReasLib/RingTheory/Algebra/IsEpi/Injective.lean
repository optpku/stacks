module

public import ReasLib.RingTheory.Algebra.IsEpi.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# Injective modules over ring epimorphisms
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat.RestrictScalars

/-- An epimorphism of commutative rings reflects injective objects along restriction of scalars. -/
theorem injective_of_epi
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    [Epi (CommRingCat.ofHom f)] (E : ModuleCat.{v} S)
    [Injective ((ModuleCat.restrictScalars.{v} f).obj E)] : Injective E := sorry

end ModuleCat.RestrictScalars
