/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.Trace.RestrictScalars
import StacksCheckRecall

@[expose] public section

universe u v w

namespace LinearMap

variable (R : Type u) {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]

section TraceRestrictScalars

variable [AddCommMonoid A] [Module R A] [Module S A] [IsScalarTower R S A]
variable [Module.Free R S] [Module.Free S A]

/- Lemma 9.20.4 (1) (Tag 0BII): the trace of an `S`-linear endomorphism after restricting
scalars from `S` to `R` is the algebra trace of its `S`-linear trace. This exact, reusable
statement is owned by `LinearMap.trace_restrictScalars`. -/
@[stacks 0BII]
#check (trace_restrictScalars R :
  (f : A →ₗ[S] A) → trace R A (f.restrictScalars R) = Algebra.trace R S (trace S A f))

end TraceRestrictScalars

section DetRestrictScalars

variable [AddCommGroup A] [Module R A] [Module S A] [IsScalarTower R S A]
variable [Module.Free R S] [Module.Free S A]
variable (f : A →ₗ[S] A)

/- Lemma 9.20.4 (2): the determinant comparison is the existing mathlib owner theorem
`LinearMap.det_restrictScalars`. -/
#check (det_restrictScalars (R := R) (S := S) (f := f) :
  (f.restrictScalars R).det = Algebra.norm R f.det)

end DetRestrictScalars

end LinearMap
