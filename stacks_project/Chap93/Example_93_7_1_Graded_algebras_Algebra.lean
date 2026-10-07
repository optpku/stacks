module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Finite projective commutative graded algebras

A commutative `ℕ`-graded algebra is finite projective in each degree when every
homogeneous piece is a finite projective module over the base ring.
-/

@[expose] public section

universe u

namespace GradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- A commutative `ℕ`-grading is finite projective when every homogeneous piece is a
finite projective module. -/
class IsFiniteProjective (𝒜 : ℕ → Submodule R A) : Prop where
  /-- Each homogeneous piece is a finite module. -/
  finite (d : ℕ) : Module.Finite R (𝒜 d)
  /-- Each homogeneous piece is a projective module. -/
  projective (d : ℕ) : Module.Projective R (𝒜 d)

/-- Finite projectivity of a grading is finiteness and projectivity of every piece. -/
theorem isFiniteProjective_iff (𝒜 : ℕ → Submodule R A) :
    IsFiniteProjective 𝒜 ↔ ∀ d, Module.Finite R (𝒜 d) ∧ Module.Projective R (𝒜 d) := sorry

namespace IsFiniteProjective

variable (𝒜 : ℕ → Submodule R A)

/-- Finite projectivity implies each homogeneous piece is finite. -/
instance instFinite [IsFiniteProjective 𝒜] (d : ℕ) : Module.Finite R (𝒜 d) :=
  IsFiniteProjective.finite d

/-- Finite projectivity implies each homogeneous piece is projective. -/
instance instProjective [IsFiniteProjective 𝒜] (d : ℕ) : Module.Projective R (𝒜 d) :=
  IsFiniteProjective.projective d

variable {k : Type u} [Field k] [Algebra k A]

/-- Over a field, finite-dimensional homogeneous pieces are finite projective. -/
instance instOfFiniteOverField (𝒜 : ℕ → Submodule k A) [∀ d, Module.Finite k (𝒜 d)] :
    IsFiniteProjective 𝒜 where
  finite d := inferInstance
  projective d := sorry

end IsFiniteProjective

end GradedAlgebra

/-- A commutative `ℕ`-graded algebra whose homogeneous pieces are finite projective. -/
structure FiniteProjectiveGradedAlgebra (R : Type u) [CommRing R] where
  /-- Underlying commutative algebra. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]
  /-- Internal `ℕ`-grading by submodules. -/
  grading : ℕ → Submodule R carrier
  [gradedAlgebra : GradedAlgebra grading]
  [isFiniteProjective : GradedAlgebra.IsFiniteProjective grading]

attribute [instance] FiniteProjectiveGradedAlgebra.commRing FiniteProjectiveGradedAlgebra.algebra
  FiniteProjectiveGradedAlgebra.gradedAlgebra FiniteProjectiveGradedAlgebra.isFiniteProjective

namespace FiniteProjectiveGradedAlgebra

variable {R : Type u} [CommRing R]

/-- Bundle a commutative `ℕ`-graded algebra with finite projective pieces. -/
def of (A : Type u) [CommRing A] [Algebra R A] (grading : ℕ → Submodule R A)
    [GradedAlgebra grading] [GradedAlgebra.IsFiniteProjective grading] :
    FiniteProjectiveGradedAlgebra R where
  carrier := A
  grading := grading

/-- The bundled object recovers the supplied carrier. -/
theorem of_carrier (A : Type u) [CommRing A] [Algebra R A] (grading : ℕ → Submodule R A)
    [GradedAlgebra grading] [GradedAlgebra.IsFiniteProjective grading] :
    (of A grading).carrier = A := sorry

/-- The bundled object recovers the supplied grading. -/
theorem of_grading (A : Type u) [CommRing A] [Algebra R A] (grading : ℕ → Submodule R A)
    [GradedAlgebra grading] [GradedAlgebra.IsFiniteProjective grading] :
    (of A grading).grading = grading := sorry

/-- A finite projective graded algebra is internally graded with finite projective pieces. -/
theorem spec (P : FiniteProjectiveGradedAlgebra R) :
    GradedAlgebra.IsFiniteProjective P.grading ∧
      (∀ d, Module.Finite R (P.grading d)) ∧
      ∀ d, Module.Projective R (P.grading d) := sorry

/-- Each homogeneous piece of a bundled finite projective graded algebra is finite. -/
instance instFinite (P : FiniteProjectiveGradedAlgebra R) (d : ℕ) :
    Module.Finite R (P.grading d) :=
  inferInstance

/-- Each homogeneous piece of a bundled finite projective graded algebra is projective. -/
instance instProjective (P : FiniteProjectiveGradedAlgebra R) (d : ℕ) :
    Module.Projective R (P.grading d) :=
  inferInstance

end FiniteProjectiveGradedAlgebra
