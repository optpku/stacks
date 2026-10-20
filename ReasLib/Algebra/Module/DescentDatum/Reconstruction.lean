module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.Algebra.Amitsur.Acyclic
public import ReasLib.Algebra.Module.DescentDatum.Effectivity

/-!
# Reconstruction of a module from descent invariants

This file defines the degree-zero invariant submodule of a module descent datum
and its canonical scalar-extension map back to the underlying module.
-/

@[expose] public section

noncomputable section

open ModuleCat
open scoped TensorProduct TensorProduct.Right

namespace Module.DescentDatum

universe u

variable {R A N : Type u}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup N] [Module R N] [Module A N]
variable [IsScalarTower R A N] [SMulCommClass R A N]

/-- The degree-zero invariant module of a descent datum, consisting of the
elements `n` satisfying `1 ⊗ₜ[R] n = D.equiv (n ⊗ₜ[R] 1)`. -/
noncomputable def h0Module (D : DescentDatum R A N) : Submodule R N :=
  LinearMap.ker <|
    (TensorProduct.mk R A N) 1 -
      (D.equiv.toLinearMap.restrictScalars R).comp
        ((TensorProduct.mk R N A).flip 1)

/-- Membership in the degree-zero invariant module is equivalent to the
descent-invariance equation. -/
theorem mem_h0Module_iff (D : DescentDatum R A N) (n : N) :
    n ∈ D.h0Module ↔
      (1 : A) ⊗ₜ[R] n = D.equiv (n ⊗ₜ[R] (1 : A)) := sorry

/-- The canonical map `A ⊗[R] H⁰(D) ⟶ N`, obtained by adjoint transposition
of the inclusion of the invariant submodule. -/
noncomputable def reconstruction (D : DescentDatum R A N) :
    (extendScalars (algebraMap R A)).obj (ModuleCat.of R D.h0Module) ⟶
      ModuleCat.of A N :=
  ((extendRestrictScalarsAdj (algebraMap R A)).homEquiv
      (ModuleCat.of R D.h0Module) (ModuleCat.of A N)).symm <|
    ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A N))
      { toFun := D.h0Module.subtype.toFun
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r m ↦ (IsScalarTower.algebraMap_smul A r (m : N)).symm }

/-- The reconstruction map sends `a ⊗ₜ[R] m` to `a • m.1`. -/
theorem reconstruction_tmul (D : DescentDatum R A N) (a : A) (m : D.h0Module) :
    D.reconstruction (a ⊗ₜ[R] m) = a • m.1 := sorry

/-- A descent datum along a faithfully flat algebra is effective exactly when
its canonical reconstruction morphism is an isomorphism. -/
theorem isEffective_iff_isIso_reconstruction [Module.FaithfullyFlat R A]
    (D : DescentDatum R A N) :
    D.IsEffective ↔ CategoryTheory.IsIso D.reconstruction := sorry

end Module.DescentDatum
