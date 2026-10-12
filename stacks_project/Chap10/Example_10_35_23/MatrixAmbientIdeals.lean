/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import stacks_project.Chap10.Example_10_35_23.CoordinateRings

/-!
# Ambient matrix ideals for Example 10.35.23

@stack 00GF

The ambient ideals, coordinate embeddings, support statements, kernel equalities, and primality
conditions remain explicit; proof obligations are deferred at the statement stage.
-/

@[expose] public section

open Matrix MvPolynomial PrimeSpectrum

universe u

noncomputable section

section

variable (k : Type u) [Field k]

/-- Helper for Example 10.35.23: the ambient ideal cutting out the `Y = 0` stratum before
passing to the quotient coordinate ring. -/
def matrixProductAmbientYIdeal :
    Ideal (MvPolynomial (Fin 2 × Fin 2 × Fin 2) k) :=
  Ideal.span <| Set.range fun ij : Fin 2 × Fin 2 ↦
    (matrixProductPolynomialMatrix k 1) ij.1 ij.2

/-- Helper for Example 10.35.23: the ambient ideal cutting out the `X = 0` stratum before
passing to the quotient coordinate ring. -/
def matrixProductAmbientXIdeal :
    Ideal (MvPolynomial (Fin 2 × Fin 2 × Fin 2) k) :=
  Ideal.span <| Set.range fun ij : Fin 2 × Fin 2 ↦
    (matrixProductPolynomialMatrix k 0) ij.1 ij.2

/-- Helper for Example 10.35.23: the embedding of the `X`-coordinates into the ambient polynomial
ring of `(X, Y)`. -/
def matrixProductXVariableEmbedding :
    Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2 := fun ij ↦ (0, ij.1, ij.2)

/-- Helper for Example 10.35.23: the embedding of the `Y`-coordinates into the ambient polynomial
ring of `(X, Y)`. -/
def matrixProductYVariableEmbedding :
    Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2 := fun ij ↦ (1, ij.1, ij.2)

/-- Helper for Example 10.35.23: the `X`-coordinate embedding is injective. -/
theorem matrixProductXVariableEmbedding_injective :
    Function.Injective (matrixProductXVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) := sorry
/-- Helper for Example 10.35.23: the `Y`-coordinate embedding is injective. -/
theorem matrixProductYVariableEmbedding_injective :
    Function.Injective (matrixProductYVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) := sorry
/-- Helper for Example 10.35.23: keeping only the `X`-variables kills the `Y`-variables. -/
def matrixProductKeepX :
    MvPolynomial (Fin 2 × Fin 2 × Fin 2) k →ₐ[k] MvPolynomial (Fin 2 × Fin 2) k :=
  MvPolynomial.killCompl matrixProductXVariableEmbedding_injective

/-- Helper for Example 10.35.23: keeping only the `Y`-variables kills the `X`-variables. -/
def matrixProductKeepY :
    MvPolynomial (Fin 2 × Fin 2 × Fin 2) k →ₐ[k] MvPolynomial (Fin 2 × Fin 2) k :=
  MvPolynomial.killCompl matrixProductYVariableEmbedding_injective

/-- Helper for Example 10.35.23: the defining relations `XY = 0` already vanish modulo `Y = 0` in
the ambient polynomial ring. -/
theorem matrixProductCoordinateRingIdeal_le_ambientYIdeal :
    matrixProductCoordinateRingIdeal k ≤ matrixProductAmbientYIdeal k := sorry
/-- Helper for Example 10.35.23: the defining relations `XY = 0` already vanish modulo `X = 0` in
the ambient polynomial ring. -/
theorem matrixProductCoordinateRingIdeal_le_ambientXIdeal :
    matrixProductCoordinateRingIdeal k ≤ matrixProductAmbientXIdeal k := sorry
/-- Helper for Example 10.35.23: if no `Y`-coordinate occurs in a monomial, then that monomial is
supported on the `X`-coordinate embedding. -/
theorem matrixProduct_support_subset_xEmbedding_of_no_y
    {m : (Fin 2 × Fin 2 × Fin 2) →₀ ℕ}
    (hm : ∀ ij : Fin 2 × Fin 2, m (1, ij.1, ij.2) = 0) :
    ↑m.support ⊆ Set.range (matrixProductXVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) := sorry
/-- Helper for Example 10.35.23: if no `X`-coordinate occurs in a monomial, then that monomial is
supported on the `Y`-coordinate embedding. -/
theorem matrixProduct_support_subset_yEmbedding_of_no_x
    {m : (Fin 2 × Fin 2 × Fin 2) →₀ ℕ}
    (hm : ∀ ij : Fin 2 × Fin 2, m (0, ij.1, ij.2) = 0) :
    ↑m.support ⊆ Set.range (matrixProductYVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) := sorry
/-- Helper for Example 10.35.23: killing the `Y`-variables has kernel exactly the ambient
`Y = 0` ideal. -/
theorem matrixProductKeepX_ker :
    RingHom.ker (matrixProductKeepX k) = matrixProductAmbientYIdeal k := sorry
/-- Helper for Example 10.35.23: killing the `X`-variables has kernel exactly the ambient
`X = 0` ideal. -/
theorem matrixProductKeepY_ker :
    RingHom.ker (matrixProductKeepY k) = matrixProductAmbientXIdeal k := sorry
/-- Helper for Example 10.35.23: the ambient `Y = 0` ideal is prime because its quotient is a
polynomial ring in the `X`-coordinates. -/
theorem matrixProductAmbientYIdeal_isPrime :
    (matrixProductAmbientYIdeal k).IsPrime := sorry
/-- Helper for Example 10.35.23: the ambient `X = 0` ideal is prime because its quotient is a
polynomial ring in the `Y`-coordinates. -/
theorem matrixProductAmbientXIdeal_isPrime :
    (matrixProductAmbientXIdeal k).IsPrime := sorry
end

#check @matrixProductXVariableEmbedding_injective
#check @matrixProductYVariableEmbedding_injective
#check @matrixProductCoordinateRingIdeal_le_ambientYIdeal
#check @matrixProductCoordinateRingIdeal_le_ambientXIdeal
#check @matrixProduct_support_subset_xEmbedding_of_no_y
#check @matrixProduct_support_subset_yEmbedding_of_no_x
#check @matrixProductKeepX_ker
#check @matrixProductKeepY_ker
#check @matrixProductAmbientYIdeal_isPrime
#check @matrixProductAmbientXIdeal_isPrime
