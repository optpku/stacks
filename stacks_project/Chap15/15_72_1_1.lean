module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import StacksCheckRecall

/-!
# Degreewise tensor-Hom currying

The source identification is the standard linear equivalence `TensorProduct.lift.equiv`
specialized to three terms of cochain complexes.
-/

@[expose] public section

/-! # 15.72.1.1 (0A5Z)

@stack 0A5Z
-/

universe u

open scoped TensorProduct

variable {R : Type u} [CommRing R]
variable (K L M : CochainComplex (ModuleCat R) ℤ) (q s r : ℤ)

/- Equation 15.72.1.1: linear maps `K^{-q} ⟶ Hom(L^{-s}, M^r)` are equivalent to linear maps
`K^{-q} ⊗ L^{-s} ⟶ M^r`. -/
@[stacks 0A5Z "degreewise tensor-Hom currying"]
#check
  (TensorProduct.lift.equiv (.id R) (K.X (-q)) (L.X (-s)) (M.X r) :
    ((K.X (-q)) →ₗ[R] (L.X (-s) →ₗ[R] M.X r)) ≃ₗ[R]
      (((K.X (-q)) ⊗[R] (L.X (-s))) →ₗ[R] M.X r))
