module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Finite projective commutative graded algebras

Commutative `ℕ`-graded algebras with finite projective homogeneous pieces.
-/

@[expose] public section

universe u

namespace GradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- A grading is finite projective when every homogeneous piece is finite and projective. -/
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

/-- Each homogeneous piece of a finite projective grading is finite. -/
instance instFinite [IsFiniteProjective 𝒜] (d : ℕ) : Module.Finite R (𝒜 d) :=
  IsFiniteProjective.finite d

/-- Each homogeneous piece of a finite projective grading is projective. -/
instance instProjective [IsFiniteProjective 𝒜] (d : ℕ) : Module.Projective R (𝒜 d) :=
  IsFiniteProjective.projective d

variable {k : Type u} [Field k] [Algebra k A]

/-- Finite-dimensional homogeneous pieces over a field are finite projective. -/
instance instOfFiniteOverField (𝒜 : ℕ → Submodule k A) [∀ d, Module.Finite k (𝒜 d)] :
    IsFiniteProjective 𝒜 where
  finite d := inferInstance
  projective d := inferInstance

end IsFiniteProjective

end GradedAlgebra

/-- A commutative algebra with a specified `ℕ`-grading and finite projective pieces. -/
def FiniteProjectiveGradedAlgebra (R : Type u) [CommRing R] :=
  Σ' algebra : CommAlgCat.{u} R,
    Σ' grading : ℕ → Submodule R algebra,
      Σ' gradedAlgebra : GradedAlgebra grading, GradedAlgebra.IsFiniteProjective grading

namespace FiniteProjectiveGradedAlgebra

variable {R : Type u} [CommRing R]

/-- The underlying carrier of a finite projective graded algebra. -/
def carrier (P : FiniteProjectiveGradedAlgebra R) : Type u := P.1.carrier

/-- The commutative ring structure stored in a finite projective graded algebra. -/
instance commRing (P : FiniteProjectiveGradedAlgebra R) : CommRing P.carrier := P.1.commRing

/-- The base algebra structure stored in a finite projective graded algebra. -/
instance algebra (P : FiniteProjectiveGradedAlgebra R) : Algebra R P.carrier := P.1.algebra

/-- The homogeneous submodules of a finite projective graded algebra. -/
def grading (P : FiniteProjectiveGradedAlgebra R) : ℕ → Submodule R P.carrier := P.2.1

/-- The internal grading structure stored in a finite projective graded algebra. -/
instance gradedAlgebra (P : FiniteProjectiveGradedAlgebra R) : GradedAlgebra P.grading :=
  P.2.2.1

/-- The homogeneous pieces of a finite projective graded algebra are finite projective. -/
instance isFiniteProjective (P : FiniteProjectiveGradedAlgebra R) :
    GradedAlgebra.IsFiniteProjective P.grading := P.2.2.2

/-- Bundle a commutative graded algebra with finite projective pieces. -/
def of (A : Type u) [CommRing A] [Algebra R A] (grading : ℕ → Submodule R A)
    [GradedAlgebra grading] [GradedAlgebra.IsFiniteProjective grading] :
    FiniteProjectiveGradedAlgebra R :=
  ⟨CommAlgCat.of R A, grading, inferInstance, inferInstance⟩

/-- The bundled object recovers the supplied carrier. -/
theorem of_carrier (A : Type u) [CommRing A] [Algebra R A] (grading : ℕ → Submodule R A)
    [GradedAlgebra grading] [GradedAlgebra.IsFiniteProjective grading] :
    (of A grading).carrier = A := sorry

/-- The bundled object recovers the supplied grading. -/
theorem of_grading (A : Type u) [CommRing A] [Algebra R A] (grading : ℕ → Submodule R A)
    [GradedAlgebra grading] [GradedAlgebra.IsFiniteProjective grading] :
    (of A grading).grading = grading := sorry

/-- Every homogeneous piece of a finite projective graded algebra is finite and projective. -/
theorem spec (P : FiniteProjectiveGradedAlgebra R) :
    GradedAlgebra.IsFiniteProjective P.grading ∧
      (∀ d, Module.Finite R (P.grading d)) ∧
      ∀ d, Module.Projective R (P.grading d) := sorry

/-- Each homogeneous piece of a bundled finite projective graded algebra is finite. -/
instance instFinite (P : FiniteProjectiveGradedAlgebra R) (d : ℕ) :
    Module.Finite R (P.grading d) := inferInstance

/-- Each homogeneous piece of a bundled finite projective graded algebra is projective. -/
instance instProjective (P : FiniteProjectiveGradedAlgebra R) (d : ℕ) :
    Module.Projective R (P.grading d) := inferInstance

end FiniteProjectiveGradedAlgebra
