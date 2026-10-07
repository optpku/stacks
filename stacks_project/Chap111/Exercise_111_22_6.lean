module

public import stacks_project.Chap111.Exercise_111_22_6_Trace
public import stacks_project.Chap111.Exercise_111_22_6_Determinant
public import ReasLib.RingTheory.Flatness.LocallyFree.Finite
import StacksCheckRecall

@[expose] public section

/-!
# Exercise 111.22.6

The trace and determinant of an endomorphism of a finite locally free module are
`LinearMap.projectiveTrace` and `LinearMap.projectiveDet`. Functoriality in the
triple `(A, M, φ)` is compatibility with extension of scalars.

@stack 02DU
-/

universe u v w

open LinearMap

variable {A : Type u} {A' : Type v} {M : Type w} {N : Type w}
  [CommRing A] [CommRing A'] [Algebra A A']
  [AddCommGroup M] [Module A M] [Module.FiniteLocallyFree A M]
  [AddCommGroup N] [Module A N] [Module.FiniteLocallyFree A N]

/- Exercise 111.22.6 (1): construct Trace and det of an endomorphism of a finite
locally free module, functorially in the triple `(A, M, φ)`. -/
@[stacks 02DU] #check @projectiveTrace
@[stacks 02DU] #check @projectiveDet
@[stacks 02DU] #check @projectiveTrace_baseChange
@[stacks 02DU] #check @projectiveDet_baseChange

/- Exercise 111.22.6 (2): Trace(φ ∘ₗ ψ) = Trace(ψ ∘ₗ φ) and
det(φ ∘ₗ ψ) = det(ψ ∘ₗ φ) for maps between finite locally free modules. -/
@[stacks 02DU] #check @projectiveTrace_comp_comm
@[stacks 02DU] #check @projectiveDet_comp_comm

/- Exercise 111.22.6 (3): Trace is an `A`-linear map `End_A(M) → A`, and det is
multiplicative. -/
@[stacks 02DU] #check (projectiveTrace : (M →ₗ[A] M) →ₗ[A] A)
@[stacks 02DU] #check @projectiveDet_comp
