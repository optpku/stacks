/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Loci associated to syntomic morphisms

This module defines the closed-fiber complete-intersection locus and the open syntomic locus of a
scheme morphism, together with their behavior under arbitrary base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S S' : Scheme.{u}}

/-- The locus of points whose closed fiber local ring is a complete intersection over the residue
field of the image point. -/
def fiberCompleteIntersectionLocus (f : X ⟶ S) : Set X :=
  {x | f.closedFiberCompleteIntersectionAt x}

/-- A point belongs to the closed-fiber complete-intersection locus exactly when its closed fiber
local ring is a complete intersection over the residue field of its image. -/
theorem mem_fiberCompleteIntersectionLocus (f : X ⟶ S) (x : X) :
    x ∈ f.fiberCompleteIntersectionLocus ↔ f.closedFiberCompleteIntersectionAt x := Iff.rfl

/-- The closed-fiber complete-intersection locus of a locally finite-type morphism commutes with
arbitrary base change. -/
theorem fiberCompleteIntersectionLocus_pullback_snd
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) :
    (pullback.snd f g).fiberCompleteIntersectionLocus =
      (pullback.fst f g) ⁻¹' f.fiberCompleteIntersectionLocus := sorry

/-- The points where a scheme morphism is syntomic form an open subset of its source. -/
theorem isOpen_syntomicLocus (f : X ⟶ S) :
    IsOpen {x : X | SyntomicAt f x} := sorry

/-- The open subset of the source where a scheme morphism is syntomic. -/
def syntomicLocus (f : X ⟶ S) : X.Opens :=
  ⟨{x | SyntomicAt f x}, f.isOpen_syntomicLocus⟩

/-- A point belongs to the syntomic locus exactly when the morphism is syntomic at that point. -/
theorem mem_syntomicLocus (f : X ⟶ S) (x : X) :
    x ∈ f.syntomicLocus ↔ SyntomicAt f x := Iff.rfl

/-- For a flat, locally finitely presented morphism, syntomicity at a base-changed point is
equivalent to syntomicity at its image in the original source. -/
theorem syntomicAt_iff_of_pullback_snd
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] (g : S' ⟶ S)
    (x' : (pullback f g : Scheme)) :
    SyntomicAt (pullback.snd f g) x' ↔ SyntomicAt f ((pullback.fst f g) x') := sorry

/-- The syntomic locus of a flat, locally finitely presented morphism commutes with arbitrary base
change. -/
theorem syntomicLocus_pullback_snd
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] (g : S' ⟶ S) :
    (pullback.snd f g).syntomicLocus =
      (pullback.fst f g) ⁻¹ᵁ f.syntomicLocus := sorry

end AlgebraicGeometry.Scheme.Hom
