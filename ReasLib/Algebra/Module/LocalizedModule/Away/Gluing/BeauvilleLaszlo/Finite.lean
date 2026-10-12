/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.Faithful
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite modules over Beauville-Laszlo covers

Finite generation is detected after base change to the product of a
compatible target ring and the away localization.

@stack 0BNN
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace LocalizedModule.Away.BeauvilleLaszlo

variable {R : Type u} [CommRing R]
variable {R' : Type v} [CommRing R']

/-- If `R ⟶ R'` induces bijections on all positive principal-power
quotients, finite generation is detected after base change to `R' × R_f`. -/
@[stacks 0BNN "finite generation over a Beauville-Laszlo cover"]
theorem finite_iff_tensorProduct_prod_of_principalPowerQuotientMap_bijective
    (φ : R →+* R') (f : R)
    (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap φ f n))
    {M : Type w} [AddCommGroup M] [Module R M] :
    let _ : Algebra R R' := φ.toAlgebra
    Module.Finite R M ↔
      Module.Finite (R' × Localization.Away f)
        ((R' × Localization.Away f) ⊗[R] M) := sorry

/-- If a module becomes finite after base change to the product of the
principal-adic completion and the away localization, it was already finite. -/
@[stacks 0BNN "finite generation from principal-adic gluing data"]
theorem finite_of_tensorProduct_principalAdicCompletion_prod
    (f : R) {M : Type w} [AddCommGroup M] [Module R M]
    (hM : Module.Finite
      (principalAdicCompletion f × Localization.Away f)
      ((principalAdicCompletion f × Localization.Away f) ⊗[R] M)) :
    Module.Finite R M := sorry

end LocalizedModule.Away.BeauvilleLaszlo
