module

public import ReasLib.Algebra.Category.ModuleCat.DualNumber.Ext
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped DualNumber

universe u

namespace DualNumber

/- Example 48.3.4: if `k` is a field, then the Ext groups of the residue module of the
dual numbers with itself are nontrivial in every natural degree. -/
@[stacks 0A9H] #check
  (DualNumber.residueExt_nontrivial :
    ∀ (k : Type u) [Field k] (i : ℕ),
      Nontrivial (CategoryTheory.Abelian.Ext
        (DualNumber.residueModule k) (DualNumber.residueModule k) i))

end DualNumber
