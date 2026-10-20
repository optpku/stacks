/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import ReasLib.LinearAlgebra.QuotientByIdeal.QuotientRing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bases after reduction by an ideal

This leaf packages the canonical operation used whenever a basis is reduced modulo an ideal.
The construction is the composite of the standard tensor base-change basis and the shared
quotient-ring/tensor equivalence; downstream arguments can therefore use the data owner directly.
-/

@[expose] public section

universe u v w

namespace Module.Basis

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {ι : Type w}

/-- The basis induced on `M ⧸ (I • ⊤)` by a basis of `M` over `R`. -/
@[stacks 00DV "basis reduction modulo an ideal"]
noncomputable def quotientByIdeal (b : Module.Basis ι R M) (I : Ideal R) :
    Module.Basis ι (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
  (b.baseChange (R ⧸ I)).map (Ideal.Quotient.tensorModuleEquiv I M)

/-- The reduced basis sends each index to the quotient class of the original basis vector. -/
@[simp]
theorem quotientByIdeal_apply (b : Module.Basis ι R M) (I : Ideal R) (i : ι) :
    b.quotientByIdeal I i = Submodule.Quotient.mk (b i) := by
  simp [quotientByIdeal]

/-- Coordinates of a quotient class in the reduced basis are the quotient of the original
coordinates. -/
@[simp]
theorem quotientByIdeal_repr (b : Module.Basis ι R M) (I : Ideal R) (x : M) (i : ι) :
    (b.quotientByIdeal I).repr (Submodule.Quotient.mk x) i =
      Ideal.Quotient.mk I (b.repr x i) := by
  change (b.baseChange (R ⧸ I)).repr
      ((Ideal.Quotient.tensorModuleEquiv I M).symm (Submodule.Quotient.mk x)) i = _
  rw [Ideal.Quotient.tensorModuleEquiv_symm_mk,
    Module.Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

end Module.Basis
