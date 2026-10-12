/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.QuotientComplex

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory
namespace DerivedCategory
namespace IdealPower
namespace QuotientComplex

/- Remark 51.21.9
   For a bounded complex `M` of finite modules over a Noetherian ring, the canonical map from
   the system `M ⊗ᴸ[A] (A ⧸ I ^ (n + 1))` to the system of termwise quotients
   `M / I ^ (n + 1) M` has an inverse after a single uniform shift. -/
@[stacks 0GA5] #check
  (CategoryTheory.DerivedCategory.IdealPower.QuotientComplex.comparison_hasShiftInverse :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A],
    (I : Ideal A) → (M : CochainComplex (ModuleCat A) ℤ) →
    (∃ a : ℤ, M.IsStrictlyGE a) → (∃ b : ℤ, M.IsStrictlyLE b) →
    (∀ i : ℤ, Module.Finite A (M.X i)) →
    ∃ c : ℕ, ∃ β : (system I M).shift c ⟶ standardSystem I M,
      Pro.SequentialHom.IsShiftInverse (comparisonNatTrans I M) c β)

end QuotientComplex
end IdealPower
end DerivedCategory
end CategoryTheory
