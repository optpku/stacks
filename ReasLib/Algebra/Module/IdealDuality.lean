module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

universe u v w

namespace Module.IdealDuality

variable (R : Type u) (E : Type v) [CommRing R]
  [AddCommGroup E] [Module R E]

/-- Restriction of an `E`-valued linear form to the submodule annihilated by an ideal. -/
def restrictToTorsion (I : Ideal R) (M : Type w) [AddCommGroup M] [Module R M] :
    (M →ₗ[R] E) →ₗ[R] (Submodule.torsionBySet R M I →ₗ[R] E) :=
  LinearMap.domRestrict' (Submodule.torsionBySet R M I)

/-- Restriction to the annihilated submodule evaluates as the original linear form. -/
theorem restrictToTorsion_apply
    (I : Ideal R) (M : Type w) [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] E) (x : Submodule.torsionBySet R M I) :
    restrictToTorsion R E I M f x = f x := sorry

/-- Multiples by an ideal of `E`-valued linear forms vanish after restriction to its
annihilated submodule. -/
theorem idealSMul_le_ker_restrictToTorsion
    (I : Ideal R) (M : Type w) [AddCommGroup M] [Module R M] :
    I • (⊤ : Submodule R (M →ₗ[R] E)) ≤
      LinearMap.ker (restrictToTorsion R E I M) := sorry

/-- The restriction map from the quotient of the dual by an ideal to the dual of the
annihilated submodule. -/
def quotientDualToDualTorsion
    (I : Ideal R) (M : Type w) [AddCommGroup M] [Module R M] :
    ((M →ₗ[R] E) ⧸ I • (⊤ : Submodule R (M →ₗ[R] E))) →ₗ[R]
      (Submodule.torsionBySet R M I →ₗ[R] E) :=
  (I • (⊤ : Submodule R (M →ₗ[R] E))).liftQ
    (restrictToTorsion R E I M)
    (idealSMul_le_ker_restrictToTorsion R E I M)

/-- Restriction from the quotient dual evaluates a representative on an element of the
annihilated submodule. -/
theorem quotientDualToDualTorsion_apply_mk
    (I : Ideal R) (M : Type w) [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] E) (x : Submodule.torsionBySet R M I) :
    quotientDualToDualTorsion R E I M
        ((I • (⊤ : Submodule R (M →ₗ[R] E))).mkQ f) x = f x := sorry

/-- Precomposition with the quotient map gives a linear form annihilated by an ideal. -/
theorem precompQuotient_mem_torsion
    (I : Ideal R) (M : Type w) [AddCommGroup M] [Module R M]
    (f : (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R] E) :
    LinearMap.lcomp R E ((I • (⊤ : Submodule R M)).mkQ) f ∈
      Submodule.torsionBySet R (M →ₗ[R] E) I := sorry

/-- The map from the dual of an ideal quotient to the ideal-annihilated submodule of the
dual. -/
def dualQuotientToTorsion
    (I : Ideal R) (M : Type w) [AddCommGroup M] [Module R M] :
    ((M ⧸ I • (⊤ : Submodule R M)) →ₗ[R] E) →ₗ[R]
      Submodule.torsionBySet R (M →ₗ[R] E) I :=
  (LinearMap.lcomp R E ((I • (⊤ : Submodule R M)).mkQ)).codRestrict
    (Submodule.torsionBySet R (M →ₗ[R] E) I)
    (precompQuotient_mem_torsion R E I M)

/-- The dual quotient comparison evaluates by applying the original form to the quotient
class of the argument. -/
theorem dualQuotientToTorsion_apply
    (I : Ideal R) (M : Type w) [AddCommGroup M] [Module R M]
    (f : (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R] E) (x : M) :
    (dualQuotientToTorsion R E I M f : M →ₗ[R] E) x =
      f ((I • (⊤ : Submodule R M)).mkQ x) := sorry

/-- Precomposition with the quotient map identifies the dual of an ideal quotient with the
ideal-annihilated submodule of the dual. -/
theorem dualQuotientToTorsion_bijective
    (I : Ideal R) (M : Type w) [AddCommGroup M] [Module R M] :
    Function.Bijective (dualQuotientToTorsion R E I M) := sorry

end Module.IdealDuality
