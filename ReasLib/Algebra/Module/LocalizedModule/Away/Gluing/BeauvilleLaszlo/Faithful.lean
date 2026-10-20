/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.RingTheory.AdicCompletion.Principal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor faithfulness for Beauville-Laszlo covers

Compatible positive principal-power quotients make the two-branch module
`R' × R_f` tensor-faithful over `R`.

@stack 0BNL
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace LocalizedModule.Away.BeauvilleLaszlo

variable {R : Type u} [CommRing R]
variable {R' : Type v} [CommRing R']

/-- If `R ⟶ R'` induces bijections on all positive principal-power
quotients, tensoring a nontrivial module with `R' × R_f` remains
nontrivial. -/
@[stacks 0BNL "tensor faithfulness of a Beauville-Laszlo cover"]
theorem tensorProduct_prod_nontrivial_of_principalPowerQuotientMap_bijective
    (φ : R →+* R') (f : R)
    (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap φ f n))
    {M : Type w} [AddCommGroup M] [Module R M] [Nontrivial M] :
    let _ : Algebra R R' := φ.toAlgebra
    Nontrivial (M ⊗[R] (R' × Localization.Away f)) := sorry

/-- Tensoring a nontrivial module with the product of the principal-adic
completion and the away localization remains nontrivial. -/
@[stacks 0BNL "tensor faithfulness for a principal-adic completion"]
theorem tensorProduct_principalAdicCompletion_prod_nontrivial
    (f : R) {M : Type w} [AddCommGroup M] [Module R M] [Nontrivial M] :
    Nontrivial
      (M ⊗[R] (principalAdicCompletion f × Localization.Away f)) := sorry

end LocalizedModule.Away.BeauvilleLaszlo
