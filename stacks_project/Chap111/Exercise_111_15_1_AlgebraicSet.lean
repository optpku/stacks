/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.AlgebraicSet

/-!
# Algebraic sets in classical affine space

A subset of the `k`-points of affine space is algebraic when it is the zero
locus of an ideal of polynomials, equivalently the common vanishing set of a
collection of polynomials.
-/

@[expose]
public section

universe u v

namespace MvPolynomial

variable {σ : Type v} {k : Type u} [Field k]

#check (MvPolynomial.IsAlgebraicSet : Set (σ → k) → Prop)

#check (MvPolynomial.isAlgebraicSet_iff : ∀ Z : Set (σ → k),
  IsAlgebraicSet Z ↔
    ∃ S : Set (MvPolynomial σ k), Z = {x | ∀ p ∈ S, aeval x p = 0})

#check (MvPolynomial.isAlgebraicSet_zeroLocus : ∀ I : Ideal (MvPolynomial σ k),
  IsAlgebraicSet (zeroLocus k I))

end MvPolynomial
