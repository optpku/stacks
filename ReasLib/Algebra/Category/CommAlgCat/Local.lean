/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.LocalCategory

/-!
# Local algebras and local algebra maps

This module defines the category of local algebras over a fixed commutative ring, with local
algebra homomorphisms as its arrows.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace LocalAlgCat

variable (A : Type u) [CommRing A]

/-- Construct a local `A`-algebra object from its canonical typeclass data. -/
def of (T : Type v) [CommRing T] [Algebra A T] [IsLocalRing T]
    [IsLocalHom (algebraMap A T)] : LocalAlgCat.{v} A :=
  ⟨⟨CommAlgCat.of A T, inferInstance, inferInstance⟩⟩

/-- The underlying carrier type of a local algebra object. -/
abbrev carrier (T : LocalAlgCat.{v} A) : Type v := T.obj.obj

/-- A local algebra object coerces to its underlying carrier type. -/
instance : CoeSort (LocalAlgCat.{v} A) (Type v) := ⟨carrier A⟩

/-- The underlying commutative ring structure of a local algebra object. -/
instance commRing (T : LocalAlgCat.{v} A) : CommRing T :=
  inferInstanceAs (CommRing T.obj.obj)

/-- The underlying `A`-algebra structure of a local algebra object. -/
instance algebra (T : LocalAlgCat.{v} A) : Algebra A T :=
  inferInstanceAs (Algebra A T.obj.obj)

/-- Every object of `LocalAlgCat A` has a local underlying ring. -/
instance isLocalRing (T : LocalAlgCat.{v} A) : IsLocalRing T := T.obj.property.1

/-- The structure map of every object of `LocalAlgCat A` is local. -/
instance algebraMapIsLocal (T : LocalAlgCat.{v} A) : IsLocalHom (algebraMap A T) :=
  T.obj.property.2

/-- Construct a morphism of local `A`-algebras from an explicit local algebra map. -/
def ofHom {T U : LocalAlgCat.{v} A}
    (f : AlgHom.Local (R := A) (A := T) (B := U)) : T ⟶ U :=
  ⟨ObjectProperty.homMk (CommAlgCat.ofHom f.hom), f.isLocal⟩

namespace Hom

/-- Regard a morphism of local `A`-algebras as an explicit local algebra map. -/
def toLocal {T U : LocalAlgCat.{v} A} (f : T ⟶ U) :
    AlgHom.Local (R := A) (A := T) (B := U) where
  hom := f.hom.hom.hom
  isLocal := f.property

/-- The underlying algebra homomorphism of `toLocal f` is the map underlying `f`. -/
theorem toLocal_hom {T U : LocalAlgCat.{v} A} (f : T ⟶ U) :
    (toLocal (A := A) f).hom = f.hom.hom.hom := sorry

end Hom

/-- The underlying local map of a morphism in `LocalAlgCat A` is local. -/
instance homIsLocal {T U : LocalAlgCat.{v} A} (f : T ⟶ U) :
    IsLocalHom f.hom.hom.hom.toRingHom := f.property

/-- Constructing a local algebra object preserves its carrier type definitionally. -/
theorem carrier_of (T : Type v) [CommRing T] [Algebra A T] [IsLocalRing T]
    [IsLocalHom (algebraMap A T)] : carrier A (of A T) = T := sorry

end LocalAlgCat
