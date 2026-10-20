module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.IsTensorProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exterior algebras and base change

@stack 0C6F
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace IsBaseChange

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module R N] [Module A N]
variable [IsScalarTower R A N]
variable {f : M →ₗ[R] N}

/-- Exterior algebra commutes with an arbitrary module base change. -/
@[stacks 0C6F "exterior algebra under module base change"]
noncomputable def exteriorAlgebraEquiv (h : IsBaseChange A f) :
    A ⊗[R] ExteriorAlgebra R M ≃ₐ[A] ExteriorAlgebra A N := by
  letI : Algebra R (ExteriorAlgebra A N) :=
    Algebra.compHom (ExteriorAlgebra A N) (algebraMap R A)
  letI : IsScalarTower R A (ExteriorAlgebra A N) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let forward : A ⊗[R] ExteriorAlgebra R M →ₐ[A] ExteriorAlgebra A N :=
    AlgHom.liftEquiv R A (ExteriorAlgebra R M) (ExteriorAlgebra A N)
      (ExteriorAlgebra.lift R
        ⟨((ExteriorAlgebra.ι A).restrictScalars R).comp f,
          fun m => ExteriorAlgebra.ι_sq_zero (f m)⟩)
  let inverse : ExteriorAlgebra A N →ₐ[A] A ⊗[R] ExteriorAlgebra R M :=
    ExteriorAlgebra.lift A
      ⟨((ExteriorAlgebra.ι R).baseChange A).comp h.equiv.symm.toLinearMap, by sorry⟩
  exact AlgEquiv.ofAlgHom forward inverse (by sorry) (by sorry)

/-- The exterior-algebra base-change equivalence on source generators. -/
@[simp, stacks 0C6F "exterior algebra base change on generators"]
theorem exteriorAlgebraEquiv_tmul_ι (h : IsBaseChange A f) (a : A) (m : M) :
    h.exteriorAlgebraEquiv (a ⊗ₜ[R] ExteriorAlgebra.ι R m) =
      a • ExteriorAlgebra.ι A (f m) := sorry

/-- The inverse exterior-algebra equivalence on arbitrary target generators. -/
@[simp, stacks 0C6F "inverse exterior algebra base change on generators"]
theorem exteriorAlgebraEquiv_symm_apply_ι (h : IsBaseChange A f) (x : N) :
    h.exteriorAlgebraEquiv.symm (ExteriorAlgebra.ι A x) =
      (ExteriorAlgebra.ι R).baseChange A (h.equiv.symm x) := sorry

end IsBaseChange
