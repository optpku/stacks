module

public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

universe u

open CategoryTheory

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- Categorical Artinian objects in `ModuleCat R` are exactly modules satisfying the
descending chain condition. -/
theorem isArtinianObject_iff (M : ModuleCat.{u} R) :
    IsArtinianObject M ↔ IsArtinian R M := sorry

/-- Categorical Noetherian objects in `ModuleCat R` are exactly modules satisfying the
ascending chain condition. -/
theorem isNoetherianObject_iff (M : ModuleCat.{u} R) :
    IsNoetherianObject M ↔ IsNoetherian R M := sorry

end ModuleCat

/-- The full category of `R`-modules satisfying the descending chain condition. -/
abbrev ArtinianModuleCat (R : Type u) [CommRing R] :=
  (isArtinianObject : ObjectProperty (ModuleCat.{u} R)).FullSubcategory

/-- The full category of `R`-modules satisfying the ascending chain condition. -/
abbrev NoetherianModuleCat (R : Type u) [CommRing R] :=
  (isNoetherianObject : ObjectProperty (ModuleCat.{u} R)).FullSubcategory

/-- The carrier type of an Artinian module object. -/
@[reducible]
def ArtinianModuleCat.carrier {R : Type u} [CommRing R]
    (M : ArtinianModuleCat R) : Type u := M.obj.carrier

/-- An Artinian module object coerces to its carrier type. -/
instance ArtinianModuleCat.instCoeSort {R : Type u} [CommRing R] :
    CoeSort (ArtinianModuleCat R) (Type u) := ⟨ArtinianModuleCat.carrier⟩

attribute [coe] ArtinianModuleCat.carrier

/-- The carrier type of a Noetherian module object. -/
@[reducible]
def NoetherianModuleCat.carrier {R : Type u} [CommRing R]
    (M : NoetherianModuleCat R) : Type u := M.obj.carrier

/-- A Noetherian module object coerces to its carrier type. -/
instance NoetherianModuleCat.instCoeSort {R : Type u} [CommRing R] :
    CoeSort (NoetherianModuleCat R) (Type u) := ⟨NoetherianModuleCat.carrier⟩

attribute [coe] NoetherianModuleCat.carrier

namespace ArtinianModuleCat

/-- Bundle an ordinary module satisfying the descending chain condition. -/
abbrev of (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [IsArtinian R M] : ArtinianModuleCat R :=
  ⟨ModuleCat.of R M, ((ModuleCat.isArtinianObject_iff R _).2 inferInstance).prop⟩

/-- An object of `ArtinianModuleCat R` is categorically Artinian. -/
instance instIsArtinianObject {R : Type u} [CommRing R] (M : ArtinianModuleCat R) :
    IsArtinianObject M.obj := sorry

/-- The underlying module of an Artinian module object satisfies the descending chain condition. -/
instance instIsArtinian {R : Type u} [CommRing R] (M : ArtinianModuleCat R) :
    IsArtinian R M := sorry

end ArtinianModuleCat

namespace NoetherianModuleCat

/-- Bundle an ordinary module satisfying the ascending chain condition. -/
abbrev of (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [IsNoetherian R M] : NoetherianModuleCat R :=
  ⟨ModuleCat.of R M, ((ModuleCat.isNoetherianObject_iff R _).2 inferInstance).prop⟩

/-- Bundle a finite module over a Noetherian ring as a Noetherian module object. -/
abbrev ofFinite (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    NoetherianModuleCat R := of R M

/-- An object of `NoetherianModuleCat R` is categorically Noetherian. -/
instance instIsNoetherianObject {R : Type u} [CommRing R] (M : NoetherianModuleCat R) :
    IsNoetherianObject M.obj := sorry

/-- The underlying module of a Noetherian module object satisfies the ascending chain condition. -/
instance instIsNoetherian {R : Type u} [CommRing R] (M : NoetherianModuleCat R) :
    IsNoetherian R M := sorry

end NoetherianModuleCat
