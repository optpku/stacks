/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Finite

@[expose] public section

/-!
# The category of finite commutative algebras

Finite commutative algebras form the full subcategory of `CommAlgCat` defined
by module-finiteness over the base ring.
-/

universe v u

namespace CommAlgCat

/-- The category of commutative algebras that are module-finite over `R`. -/
abbrev Finite (R : Type u) [CommRing R] : Type _ :=
  (finite.{v} R).FullSubcategory

namespace Finite

variable (R : Type u) [CommRing R]

/-- The carrier of a finite commutative algebra is its underlying algebra's carrier. -/
instance instCoeSort : CoeSort (Finite.{v} R) (Type v) :=
  ⟨fun algebra ↦ algebra.obj⟩

/-- A finite commutative algebra is module-finite over its base ring. -/
instance instModuleFinite (S : Finite.{v} R) : Module.Finite R S :=
  S.property

/-- Bundle a commutative algebra that is module-finite over its base ring. -/
abbrev of (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S] :
    Finite.{v} R where
  obj := CommAlgCat.of R S
  property := inferInstance

end Finite

end CommAlgCat
