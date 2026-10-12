/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Flat.MvPolynomial
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open MvPolynomial
open scoped TensorProduct

namespace MvPolynomial

/- Exercise 111.5.2 (1): find an injection whose tensor is not injective for
the variable ideal in `k[X, Y]`. -/
@[stacks 02CR] #check
  (MvPolynomial.idealOfVars_subtype_rTensor_idealOfVars_not_injective :
    ∀ (k : Type u) [Field k],
      ¬ Function.Injective
        ((idealOfVars (Fin 2) k).subtype.rTensor (idealOfVars (Fin 2) k)))

#check
  (MvPolynomial.not_flat_idealOfVars :
    ∀ (k : Type u) [Field k],
      ¬ Module.Flat (MvPolynomial (Fin 2) k) (idealOfVars (Fin 2) k))

/- Exercise 111.5.2 (2): find an injection whose tensor is not injective for
the quotient by the variable ideal in `k[X, Y]`. -/
@[stacks 02CR] #check
  (MvPolynomial.idealOfVars_subtype_rTensor_quotient_not_injective :
    ∀ (k : Type u) [Field k],
      ¬ Function.Injective
        ((idealOfVars (Fin 2) k).subtype.rTensor
          (MvPolynomial (Fin 2) k ⧸ idealOfVars (Fin 2) k)))

#check
  (MvPolynomial.not_flat_quotient_idealOfVars :
    ∀ (k : Type u) [Field k],
      ¬ Module.Flat (MvPolynomial (Fin 2) k)
          (MvPolynomial (Fin 2) k ⧸ idealOfVars (Fin 2) k))

end MvPolynomial
