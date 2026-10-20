module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Lifting squares of commutative rings

This file packages the data of a commutative square and a diagonal lift.  It
parallels `CategoryTheory.CommSq`, while retaining independent universes for
the four raw ring carriers.  It is independent of any particular
infinitesimal extension predicate, so deformation-theoretic lifting criteria
can share the same API.

@stack 0DYG
-/

universe u v w x

namespace RingHom

/-- A commutative square with left map `f` and right map `π`. -/
@[stacks 0DYG "commutative ring lifting square"]
structure LiftingSquare {R : Type u} {S : Type v} {A' : Type w} {A : Type x}
    [Semiring R] [Semiring S] [Semiring A'] [Semiring A]
    (f : R →+* S) (π : A' →+* A) where
  /-- The upper horizontal map of the square. -/
  upper : R →+* A'
  /-- The lower horizontal map of the square. -/
  lower : S →+* A
  /-- Commutativity of the square. -/
  comm : π.comp upper = lower.comp f

/-- Construct a lifting square from its two horizontal maps and commutativity proof. -/
def LiftingSquare.ofMaps {R : Type u} {S : Type v} {A' : Type w} {A : Type x}
    [Semiring R] [Semiring S] [Semiring A'] [Semiring A]
    {f : R →+* S} {π : A' →+* A} (upper : R →+* A') (lower : S →+* A)
    (comm : π.comp upper = lower.comp f) : LiftingSquare f π :=
  ⟨upper, lower, comm⟩

namespace LiftingSquare

/-- A diagonal lift of a commutative ring-homomorphism square. -/
@[stacks 0DYG "diagonal lift of a commutative ring square"]
structure Lift {R : Type u} {S : Type v} {A' : Type w} {A : Type x}
    [Semiring R] [Semiring S] [Semiring A'] [Semiring A]
    {f : R →+* S} {π : A' →+* A} (sq : LiftingSquare f π) where
  /-- The diagonal ring homomorphism. -/
  hom : S →+* A'
  /-- The lower-right triangle commutes. -/
  facRight : π.comp hom = sq.lower
  /-- The upper-left triangle commutes. -/
  facLeft : hom.comp f = sq.upper

/-- Construct a diagonal lift from its homomorphism and triangle identities. -/
def Lift.ofHom {R : Type u} {S : Type v} {A' : Type w} {A : Type x}
    [Semiring R] [Semiring S] [Semiring A'] [Semiring A]
    {f : R →+* S} {π : A' →+* A} (sq : LiftingSquare f π) (hom : S →+* A')
    (facRight : π.comp hom = sq.lower) (facLeft : hom.comp f = sq.upper) : sq.Lift :=
  ⟨hom, facRight, facLeft⟩

/-- A diagonal lift satisfies both triangle identities of its square. -/
theorem Lift.spec {R : Type u} {S : Type v} {A' : Type w} {A : Type x}
    [Semiring R] [Semiring S] [Semiring A'] [Semiring A]
    {f : R →+* S} {π : A' →+* A} (sq : LiftingSquare f π) (lift : sq.Lift) :
    π.comp lift.hom = sq.lower ∧ lift.hom.comp f = sq.upper :=
  ⟨lift.facRight, lift.facLeft⟩

/-- A lifting square has a lift when its type of diagonal lifts is nonempty. -/
@[stacks 0DYG "lift of a commutative ring square"]
def HasLift {R : Type u} {S : Type v} {A' : Type w} {A : Type x}
    [Semiring R] [Semiring S] [Semiring A'] [Semiring A]
    {f : R →+* S} {π : A' →+* A} (sq : LiftingSquare f π) : Prop :=
  Nonempty sq.Lift

end LiftingSquare

end RingHom
