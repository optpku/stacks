module

public import ReasLib.Algebra.Category.ModuleCat.Ext.MvPolynomial.InfiniteVariables
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open CategoryTheory Abelian MvPolynomial

namespace MvPolynomial

/- Exercise 111.11.4: for a field `k`, take `R = MvPolynomial ℕ k` and
`I = idealOfVars ℕ k`. The quotient's degree-one self-Ext is not finite over `R`. -/
@[stacks 0CRF] #check (MvPolynomial.ext_one_quotient_idealOfVars_not_finite :
    (k : Type u) → [Field k] →
      ¬ Module.Finite (MvPolynomial ℕ k)
        (Abelian.Ext
          (ModuleCat.of (MvPolynomial ℕ k) (MvPolynomial ℕ k ⧸ idealOfVars ℕ k))
          (ModuleCat.of (MvPolynomial ℕ k) (MvPolynomial ℕ k ⧸ idealOfVars ℕ k)) 1))

end MvPolynomial
