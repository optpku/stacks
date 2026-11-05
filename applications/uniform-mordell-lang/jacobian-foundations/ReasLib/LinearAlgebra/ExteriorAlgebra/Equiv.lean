module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences of exterior algebras

@stack 0FJB

A linear equivalence induces an equivalence of exterior algebras.  This file keeps that
construction at the algebraic layer, without finite-generation or projectivity assumptions, so
determinant and base-change APIs can share the same owner.
-/

@[expose] public section

noncomputable section

universe u v w

namespace ExteriorAlgebra

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The exterior-algebra maps induced by a linear equivalence and its inverse compose to the
identity on the source. -/
theorem mapEquiv_symm_comp (e : M ≃ₗ[R] N) :
    (map e.symm.toLinearMap).comp (map e.toLinearMap) =
      AlgHom.id R (ExteriorAlgebra R M) := sorry

/-- The exterior-algebra maps induced by a linear equivalence and its inverse compose to the
identity on the target. -/
theorem mapEquiv_comp_symm (e : M ≃ₗ[R] N) :
    (map e.toLinearMap).comp (map e.symm.toLinearMap) =
      AlgHom.id R (ExteriorAlgebra R N) := sorry

/-- The algebra equivalence of exterior algebras induced by a linear equivalence of modules. -/
@[stacks 0FJB "exterior algebra equivalence"]
def mapEquiv (e : M ≃ₗ[R] N) :
    ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R N :=
  AlgEquiv.ofAlgHom
    (map e.toLinearMap)
    (map e.symm.toLinearMap)
    (mapEquiv_comp_symm e)
    (mapEquiv_symm_comp e)

/-- The underlying algebra map of `mapEquiv e` is the exterior-algebra map induced by `e`. -/
@[simp]
theorem mapEquiv_toAlgHom (e : M ≃ₗ[R] N) :
    (mapEquiv e).toAlgHom = map e.toLinearMap := sorry

/-- The underlying linear map of `mapEquiv e` is the exterior-algebra map induced by `e`. -/
@[simp]
theorem mapEquiv_toLinearMap (e : M ≃ₗ[R] N) :
    (mapEquiv e).toLinearEquiv.toLinearMap = (map e.toLinearMap).toLinearMap := sorry

/-- `mapEquiv e` sends a degree-one generator to the generator indexed by its image under `e`. -/
@[simp]
theorem mapEquiv_apply_ι (e : M ≃ₗ[R] N) (m : M) :
    mapEquiv e (ι R m) = ι R (e m) := sorry

/-- The exterior-algebra equivalence induced by an inverse is the inverse equivalence. -/
@[simp]
theorem mapEquiv_symm (e : M ≃ₗ[R] N) :
    mapEquiv e.symm = (mapEquiv e).symm := sorry

/-- The identity module equivalence induces the identity exterior-algebra equivalence. -/
@[simp]
theorem mapEquiv_refl :
    mapEquiv (LinearEquiv.refl R M) = AlgEquiv.refl := sorry

/-- Exterior-algebra equivalences respect composition of module equivalences. -/
@[simp]
theorem mapEquiv_trans {P : Type*} [AddCommGroup P] [Module R P]
    (e : M ≃ₗ[R] N) (e' : N ≃ₗ[R] P) :
    mapEquiv (e.trans e') = (mapEquiv e).trans (mapEquiv e') := sorry

end ExteriorAlgebra
