module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.Finite
import StacksCheckRecall

/-!
# Lemma 15.91.4

Finite generation is detected after tensoring with the product of the
compatible base-change ring and the away localization.

@stack 0BNN
-/

@[expose] public section

open scoped TensorProduct
open LocalizedModule.Away.BeauvilleLaszlo

universe u v w

namespace Lemma_15_91_4

variable {R : Type u} [CommRing R]
variable {R' : Type v} [CommRing R']
variable (φ : R →+* R') (f : R)
variable (hquot : ∀ n : ℕ+, Function.Bijective
  (principalPowerIdealImageQuotientMap φ f n))
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Lemma 15.91.4 (0BNN): finite generation over `R` is equivalent to
finite generation after base change to `R' × R_f`. -/
@[stacks 0BNN "finite generation over a Beauville-Laszlo cover"]
#check (finite_iff_tensorProduct_prod_of_principalPowerQuotientMap_bijective
    φ f hquot :
  let _ : Algebra R R' := φ.toAlgebra
  Module.Finite R M ↔
    Module.Finite (R' × Localization.Away f)
      ((R' × Localization.Away f) ⊗[R] M))

/- In particular, finiteness after base change to the principal-adic
completion and the away localization implies finiteness over `R`. -/
@[stacks 0BNN "finite generation from principal-adic gluing data"]
#check (finite_of_tensorProduct_principalAdicCompletion_prod f :
  Module.Finite
      (principalAdicCompletion f × Localization.Away f)
      ((principalAdicCompletion f × Localization.Away f) ⊗[R] M) →
    Module.Finite R M)

end Lemma_15_91_4
