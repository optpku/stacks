/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Hom
public import ReasLib.RingTheory.RingHom.LiftingSquare

@[expose] public section

/-!
# Lifts through algebra homomorphisms

For a square already expressed over a fixed base algebra, the mathematical
data is a lift through an explicit algebra homomorphism.  This leaf keeps
that data independent of an ambient `Algebra B' B` instance or a
scalar-tower pin.

@stack 02HT
-/

universe u v w x

namespace AlgHom

/-- An `R`-algebra map `f : S →ₐ[R] B` lifts through `π : B' →ₐ[R] B` when
there is an `R`-algebra map `f' : S →ₐ[R] B'` with `π.comp f' = f`.

The explicit map `π` is part of the statement: the same pair of rings can
carry several `R`-algebra maps, so an ambient `Algebra B' B` instance would
not be a canonical owner for this lifting problem.
-/
@[stacks 02HT "algebra-level lifting payload"]
def HasLift {R : Type u} {S : Type v} {B' : Type w} {B : Type x}
    [CommSemiring R] [Semiring S] [Semiring B'] [Semiring B]
    [Algebra R S] [Algebra R B'] [Algebra R B]
    (π : B' →ₐ[R] B) (f : S →ₐ[R] B) : Prop :=
  ∃ f' : S →ₐ[R] B', π.comp f' = f

/-- The underlying ring-hom square associated to an algebra lifting problem.
The upper and lower maps are the structural algebra maps, so its
commutativity is canonical and does not require an ambient
`Algebra B' B` instance. -/
def toLiftingSquare {R : Type u} {S : Type v} {B' : Type w} {B : Type x}
    [CommSemiring R] [Semiring S] [Semiring B'] [Semiring B]
    [Algebra R S] [Algebra R B'] [Algebra R B]
    (π : B' →ₐ[R] B) (f : S →ₐ[R] B) :
    RingHom.LiftingSquare (algebraMap R S) π.toRingHom :=
  { upper := algebraMap R B'
    lower := f.toRingHom
    comm := (π.comp_algebraMap).trans f.comp_algebraMap.symm }

/-- An algebra lift gives a lift of the associated underlying ring square.
The converse is intentionally not asserted: a ring-hom lift need not respect
the fixed base algebra. -/
theorem HasLift.toRingSquare {R : Type u} {S : Type v} {B' : Type w} {B : Type x}
    [CommSemiring R] [Semiring S] [Semiring B'] [Semiring B]
    [Algebra R S] [Algebra R B'] [Algebra R B]
    (π : B' →ₐ[R] B) (f : S →ₐ[R] B)
    (h : HasLift π f) :
    (toLiftingSquare π f).HasLift := sorry

end AlgHom
