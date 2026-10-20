module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.Algebra.Homology.CochainDGAlgebra.DegreeZero.Functor
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Pro.Sequential
import Mathlib.Tactic.CrossRefAttribute

/-!
# The ideal-power quotient DGA system

For a commutative ring `R` and an ideal `I`, this file packages the positive ideal-power
quotients as a zero-based inverse system: stage `n` is `R / I ^ (n + 1)`.  Applying the
degree-zero functor gives the cochain-DGA system used by adic quasi-coherence.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite

namespace Ideal.Power

variable {R : Type u} [CommRing R]

/-- Positive stage `n` of the ideal-power quotient tower is the `R`-algebra
`R / I ^ (n + 1)`. -/
@[stacks 0GZK "positive ideal-power quotient algebra"]
abbrev quotientAlgebra (I : Ideal R) (n : ℕ) : AlgCat.{u} R :=
  AlgCat.of R (R ⧸ I ^ (n + 1))

/-- The quotient-algebra transition from exponent `n + 2` to exponent `n + 1`. -/
@[stacks 0GZK "positive ideal-power quotient transition"]
abbrev quotientTransition (I : Ideal R) (n : ℕ) :
    quotientAlgebra I (n + 1) ⟶ quotientAlgebra I n :=
  AlgCat.ofHom
    (Ideal.Quotient.factorₐ R
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))

/-- The zero-based inverse system whose stage `n` is `R / I ^ (n + 1)`. -/
@[stacks 0GZK "positive ideal-power quotient inverse system"]
noncomputable abbrev quotientSystem (I : Ideal R) : ℕᵒᵖ ⥤ AlgCat.{u} R :=
  Functor.ofOpSequence (quotientTransition I)

/-- The object at stage `n` of the positive ideal-power quotient system. -/
@[simp]
theorem quotientSystem_obj (I : Ideal R) (n : ℕ) :
    (quotientSystem I).obj (op n) = quotientAlgebra I n := sorry

/-- The generating map of the positive ideal-power quotient system is the canonical quotient
transition. -/
theorem quotientSystem_map_succ (I : Ideal R) (n : ℕ) :
    (quotientSystem I).map (homOfLE (Nat.le_add_right n 1)).op =
      quotientTransition I n := sorry

/-- For `n ≤ m`, the map from stage `m` to stage `n` is the quotient map induced by
`I ^ (m + 1) ≤ I ^ (n + 1)`. -/
@[stacks 0GZK "arbitrary transition in the ideal-power quotient system"]
theorem quotientSystem_map (I : Ideal R) {n m : ℕ} (h : n ≤ m) :
    (quotientSystem I).map (homOfLE h).op =
      AlgCat.ofHom
        (Ideal.Quotient.factorₐ R
          (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))) := sorry

/-- The positive ideal-power quotient system, regarded as degree-zero cochain DGAs. -/
@[stacks 0GZK "ideal-power quotient cochain-DGA inverse system"]
noncomputable abbrev dgaSystem (I : Ideal R) :
    ℕᵒᵖ ⥤ CochainDGAlgebra.{u, u} R :=
  quotientSystem I ⋙ CochainDGAlgebra.degreeZero R

/-- Stage `n` of the ideal-power DGA system is the degree-zero DGA on
`R / I ^ (n + 1)`. -/
@[simp]
theorem dgaSystem_obj (I : Ideal R) (n : ℕ) :
    (dgaSystem I).obj (op n) =
      CochainDGAlgebra.ofAlgebra R (R ⧸ I ^ (n + 1)) := sorry

/-- The generating transition of the ideal-power DGA system is induced by the canonical
quotient algebra homomorphism. -/
theorem dgaSystem_map_succ (I : Ideal R) (n : ℕ) :
    (dgaSystem I).map (homOfLE (Nat.le_add_right n 1)).op =
      CochainDGAlgebra.ofAlgebraHom R
        (Ideal.Quotient.factorₐ R
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) := sorry

/-- For `n ≤ m`, the DGA map from stage `m` to stage `n` is concentrated in degree zero and
induced by the canonical quotient algebra homomorphism. -/
@[stacks 0GZK "arbitrary transition in the ideal-power quotient DGA system"]
theorem dgaSystem_map (I : Ideal R) {n m : ℕ} (h : n ≤ m) :
    (dgaSystem I).map (homOfLE h).op =
      CochainDGAlgebra.ofAlgebraHom R
        (Ideal.Quotient.factorₐ R
          (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))) := sorry

/-- The pro-DGA represented by the positive ideal-power quotient system. -/
@[stacks 0GZK "ideal-power quotient pro-DGA"]
noncomputable abbrev dgaProObject (I : Ideal R) :
    CategoryTheory.Pro (CochainDGAlgebra.{u, u} R) :=
  CochainDGAlgebra.InverseSystem.proObject (dgaSystem I)

end Ideal.Power
