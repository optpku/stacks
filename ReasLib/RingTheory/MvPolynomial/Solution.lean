module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.SModEq.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Solutions of multivariate polynomial systems

This file provides a coefficient-aware predicate for a family of equations
evaluated in an arbitrary algebra.  Equation and variable indices are not
restricted to finite types.
-/

universe u v w x y

namespace MvPolynomial

/-- A tuple `a` is a solution of the polynomial system `f` when every
polynomial in the family vanishes after algebraic evaluation at `a`. -/
@[stacks 07QY "solution of a polynomial system"]
def IsSolution {σ : Type u} {ι : Type v} {R : Type w} {S : Type x}
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    (f : ι → MvPolynomial σ R) (a : σ → S) : Prop :=
  ∀ j, aeval a (f j) = 0

/-- Unfold the solution predicate into pointwise algebraic evaluation. -/
@[simp]
theorem isSolution_iff {σ : Type u} {ι : Type v} {R : Type w} {S : Type x}
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    (f : ι → MvPolynomial σ R) (a : σ → S) :
    IsSolution f a ↔ ∀ j, aeval a (f j) = 0 := sorry

/-- For a tuple in the coefficient ring, algebraic evaluation agrees with
the usual multivariate polynomial evaluation. -/
@[simp]
theorem isSolution_iff_eval {σ : Type u} {ι : Type v} {R : Type w}
    [CommSemiring R] (f : ι → MvPolynomial σ R) (a : σ → R) :
    IsSolution f a ↔ ∀ j, eval a (f j) = 0 := sorry

/-- An exact solution `a` approximates a tuple `aHat` modulo `I` when its
image under `φ` is coordinatewise congruent to `aHat` modulo `I`. -/
@[stacks 07QY "polynomial solution approximation"]
def IsApproximation {σ : Type u} {ι : Type v} {R : Type w}
    {S : Type x} {T : Type y}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : ι → MvPolynomial σ R) (aHat : σ → T)
    (φ : S →ₐ[R] T) (I : Ideal T) (a : σ → S) : Prop :=
  IsSolution f a ∧ ∀ i, aHat i ≡ φ (a i) [SMOD I]

/-- Unfold an approximate solution into exact solvability and coordinatewise
congruence. -/
@[simp]
theorem isApproximation_iff {σ : Type u} {ι : Type v} {R : Type w}
    {S : Type x} {T : Type y}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : ι → MvPolynomial σ R) (aHat : σ → T)
    (φ : S →ₐ[R] T) (I : Ideal T) (a : σ → S) :
    IsApproximation f aHat φ I a ↔
      IsSolution f a ∧ ∀ i, aHat i ≡ φ (a i) [SMOD I] := sorry

namespace IsSolution

/-- A solution remains a solution after applying an algebra homomorphism. -/
theorem map {σ : Type u} {ι : Type v} {R : Type w}
    {S : Type x} {T : Type y}
    [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Algebra R S] [Algebra R T]
    {f : ι → MvPolynomial σ R} {a : σ → S}
    (ha : IsSolution f a) (g : S →ₐ[R] T) :
    IsSolution f (fun i ↦ g (a i)) := sorry

end IsSolution

namespace IsApproximation

/-- An approximate solution is an exact solution of the polynomial system. -/
theorem isSolution {σ : Type u} {ι : Type v} {R : Type w}
    {S : Type x} {T : Type y}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    {f : ι → MvPolynomial σ R} {aHat : σ → T}
    {φ : S →ₐ[R] T} {I : Ideal T} {a : σ → S}
    (ha : IsApproximation f aHat φ I a) : IsSolution f a := sorry

/-- Each coordinate of an approximate solution has the prescribed
congruence. -/
theorem modEq {σ : Type u} {ι : Type v} {R : Type w}
    {S : Type x} {T : Type y}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    {f : ι → MvPolynomial σ R} {aHat : σ → T}
    {φ : S →ₐ[R] T} {I : Ideal T} {a : σ → S}
    (ha : IsApproximation f aHat φ I a) (i : σ) :
    aHat i ≡ φ (a i) [SMOD I] := sorry

end IsApproximation

/-- A chosen exact solution together with its approximation of a prescribed
tuple modulo an ideal. -/
@[stacks 07QY "bundled polynomial solution approximation"]
structure SolutionApproximation {σ : Type u} {ι : Type v} {R : Type w}
    {S : Type x} {T : Type y}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : ι → MvPolynomial σ R) (aHat : σ → T)
    (φ : S →ₐ[R] T) (I : Ideal T) where
  /-- The chosen exact solution. -/
  solution : σ → S
  /-- The chosen solution has the required approximation property. -/
  isApproximation : IsApproximation f aHat φ I solution

namespace SolutionApproximation

/-- Bundle a solution with its approximation property. -/
def of {σ : Type u} {ι : Type v} {R : Type w}
    {S : Type x} {T : Type y}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    {f : ι → MvPolynomial σ R} {aHat : σ → T}
    {φ : S →ₐ[R] T} {I : Ideal T} (a : σ → S)
    (ha : IsApproximation f aHat φ I a) :
    SolutionApproximation f aHat φ I :=
  ⟨a, ha⟩

/-- The solution stored by `of` is the supplied tuple. -/
@[simp]
theorem solution_of {σ : Type u} {ι : Type v} {R : Type w}
    {S : Type x} {T : Type y}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    {f : ι → MvPolynomial σ R} {aHat : σ → T}
    {φ : S →ₐ[R] T} {I : Ideal T} (a : σ → S)
    {ha : IsApproximation f aHat φ I a} :
    (of a ha).solution = a := sorry

/-- The tuple stored by a solution approximation solves the polynomial
system. -/
theorem isSolution {σ : Type u} {ι : Type v} {R : Type w}
    {S : Type x} {T : Type y}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    {f : ι → MvPolynomial σ R} {aHat : σ → T}
    {φ : S →ₐ[R] T} {I : Ideal T}
    (A : SolutionApproximation f aHat φ I) :
    IsSolution f A.solution := sorry

/-- The tuple stored by a solution approximation satisfies the prescribed
coordinatewise congruence. -/
theorem modEq {σ : Type u} {ι : Type v} {R : Type w}
    {S : Type x} {T : Type y}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    {f : ι → MvPolynomial σ R} {aHat : σ → T}
    {φ : S →ₐ[R] T} {I : Ideal T}
    (A : SolutionApproximation f aHat φ I) (i : σ) :
    aHat i ≡ φ (A.solution i) [SMOD I] := sorry

/-- A bundled solution approximation exists exactly when an approximating
exact solution exists. -/
theorem nonempty_iff_exists {σ : Type u} {ι : Type v} {R : Type w}
    {S : Type x} {T : Type y}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : ι → MvPolynomial σ R) (aHat : σ → T)
    (φ : S →ₐ[R] T) (I : Ideal T) :
    Nonempty (SolutionApproximation f aHat φ I) ↔
      ∃ a, IsApproximation f aHat φ I a := sorry

end SolutionApproximation

end MvPolynomial
