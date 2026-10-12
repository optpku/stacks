/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

universe u

/-- The Picard group of a polynomial ring over a field is subsingleton. -/
theorem CommRing.Pic.subsingletonPolynomial {k : Type u} [Field k] :
    Subsingleton (CommRing.Pic (Polynomial k)) := inferInstance

/-- The Picard group of the integers is subsingleton. -/
theorem CommRing.Pic.subsingletonInt : Subsingleton (CommRing.Pic ℤ) := inferInstance

/-- The Picard group of a two-variable polynomial ring over a field is subsingleton. -/
theorem CommRing.Pic.subsingletonMvPolynomial {k : Type u} [Field k] :
    Subsingleton (CommRing.Pic (MvPolynomial (Fin 2) k)) := inferInstance

/-- The Picard group of the nodal quotient of a two-variable polynomial ring over a field is subsingleton. -/
instance CommRing.Pic.instSubsingletonQuotientSpanMul {k : Type u} [Field k] :
    Subsingleton (CommRing.Pic (MvPolynomial (Fin 2) k ⧸
      Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k)})) :=
  sorry
