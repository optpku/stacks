module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.Faithful
import StacksCheckRecall

/-!
# Lemma 15.91.2

The pair consisting of a compatible base change and localization away from
`f` is tensor-faithful.  The recalls below give the commutative-ring
formalization and its principal-adic completion specialization.

@stack 0BNL
-/

@[expose] public section

open scoped TensorProduct
open LocalizedModule.Away.BeauvilleLaszlo

universe u v w

namespace Lemma_15_91_2

variable {R : Type u} [CommRing R]
variable {R' : Type v} [CommRing R']
variable (φ : R →+* R') (f : R)
variable (hquot : ∀ n : ℕ+, Function.Bijective
  (principalPowerIdealImageQuotientMap φ f n))
variable {M : Type w} [AddCommGroup M] [Module R M] [Nontrivial M]

/- Lemma 15.91.2 (0BNL): if all positive principal-power quotient maps are
bijective, then `M ⊗[R] (R' × R_f)` is nontrivial whenever `M` is. -/
@[stacks 0BNL "tensor faithfulness of a Beauville-Laszlo cover"]
#check (tensorProduct_prod_nontrivial_of_principalPowerQuotientMap_bijective
    φ f hquot :
  let _ : Algebra R R' := φ.toAlgebra
  Nontrivial (M ⊗[R] (R' × Localization.Away f)))

/- For the principal-adic completion the positive-power quotient hypotheses
are supplied by Lemma 15.91.1. -/
@[stacks 0BNL "tensor faithfulness for a principal-adic completion"]
#check (tensorProduct_principalAdicCompletion_prod_nontrivial f :
  Nontrivial
    (M ⊗[R] (principalAdicCompletion f × Localization.Away f)))

end Lemma_15_91_2
