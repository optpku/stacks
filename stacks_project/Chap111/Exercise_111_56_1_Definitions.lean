module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Operations
public import ReasLib.NumberTheory.FunctionField.WeilDifferential
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable (I : Ideal R) (φ : A →+* B)

/- Companion clause 1: a radical ideal of a ring, using the canonical predicate. -/
#check (Ideal.IsRadical I : Prop)

/- Companion clause 2: a finite type ring homomorphism, using the canonical predicate. -/
#check (RingHom.FiniteType φ : Prop)

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/- Exercise 111.56.1 (Definitions): the four clauses give, in source order,
a radical ideal, a finite type ring homomorphism, a differential a la Weil,
and a scheme. Clause 3 is the main entry; clauses 1, 2, and 4 are canonical
companion definitions. -/
@[stacks 09TW]
#check (FunctionField.IsWeilDifferential k K :
  (FunctionField.AdeleRing k K →ₗ[k] k) → Prop)

/- Companion clause 4: a scheme, using the canonical bundled object. -/
#check (AlgebraicGeometry.Scheme : Type (u + 1))
