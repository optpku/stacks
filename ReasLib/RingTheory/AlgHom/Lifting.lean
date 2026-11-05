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

section

variable {R : Type u} {S : Type v} {B' : Type w} {B : Type x}
    [CommSemiring R] [Semiring S] [Semiring B'] [Semiring B]
    [Algebra R S] [Algebra R B'] [Algebra R B]
    (π : B' →ₐ[R] B) (f : S →ₐ[R] B)

/-- Forget the algebra structure of a specified lift, retaining both triangles. -/
def toLiftingSquareLift (g : S →ₐ[R] B') (hg : π.comp g = f) :
    (toLiftingSquare π f).Lift where
  hom := g.toRingHom
  facRight := congrArg AlgHom.toRingHom hg
  facLeft := g.comp_algebraMap

/-- The left triangle of the structural square makes its diagonal an algebra map. -/
def ofLiftingSquareLift (l : (toLiftingSquare π f).Lift) : S →ₐ[R] B' :=
  { l.hom with
    commutes' := fun r => congrArg (fun h : R →+* B' => h r) l.facLeft }

@[simp]
theorem ofLiftingSquareLift_toRingHom (l : (toLiftingSquare π f).Lift) :
    (ofLiftingSquareLift π f l).toRingHom = l.hom := rfl

/-- The right triangle gives the factorization as algebra homomorphisms. -/
@[simp]
theorem ofLiftingSquareLift_fac (l : (toLiftingSquare π f).Lift) :
    π.comp (ofLiftingSquareLift π f l) = f := by
  apply AlgHom.ext
  intro s
  exact congrArg (fun h : S →+* B => h s) l.facRight

/-- Algebra lifts and diagonals of the structural ring square have identical data. -/
def liftingSquareLiftEquiv :
    {g : S →ₐ[R] B' // π.comp g = f} ≃ (toLiftingSquare π f).Lift where
  toFun g := toLiftingSquareLift π f g.val g.property
  invFun l := ⟨ofLiftingSquareLift π f l, ofLiftingSquareLift_fac π f l⟩
  left_inv g := by
    apply Subtype.ext
    apply AlgHom.ext
    intro s
    rfl
  right_inv l := by
    cases l
    rfl

/-- Existence of a lift is independent of its algebra or structural-square packaging. -/
theorem hasLift_iff : HasLift π f ↔ (toLiftingSquare π f).HasLift := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨toLiftingSquareLift π f g hg⟩
  · rintro ⟨l⟩
    exact ⟨ofLiftingSquareLift π f l, ofLiftingSquareLift_fac π f l⟩

end

/-- An algebra lift gives a lift of the associated underlying ring square.
For the converse, use `AlgHom.hasLift_iff`: its left triangle enforces
compatibility with the fixed base algebra. -/
theorem HasLift.toRingSquare {R : Type u} {S : Type v} {B' : Type w} {B : Type x}
    [CommSemiring R] [Semiring S] [Semiring B'] [Semiring B]
    [Algebra R S] [Algebra R B'] [Algebra R B]
    (π : B' →ₐ[R] B) (f : S →ₐ[R] B)
    (h : HasLift π f) :
    (toLiftingSquare π f).HasLift :=
  (hasLift_iff π f).mp h

end AlgHom
