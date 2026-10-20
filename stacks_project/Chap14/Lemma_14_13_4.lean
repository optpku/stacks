module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.StdSimplex
import StacksCheckRecall

/-!
@stack 017F
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject
open SSet.stdSimplex
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section Full

variable (k : ℕ) (X : C) (V : SimplicialObject C)
variable [HasCopower (Δ[k] : SSet.{w}) ((SimplicialObject.const C).obj X)]

/- The reusable owner is the category-generic coproduct-side Yoneda equivalence. -/
#check Functor.indexedCoprod.uliftYoneda.homEquiv

/- Lemma 14.13.4 (1): maps from the standard-simplex copower by `X` are maps from `X`
into degree `k`. -/
@[stacks 017F "Lemma 14.13.4 (1)"]
#check (SimplicialObject.copower.stdSimplex.homEquiv k X V :
  (SimplicialObject.copower (Δ[k] : SSet.{w}) ((SimplicialObject.const C).obj X) ⟶ V) ≃
    (X ⟶ V.obj (op ⦋k⦌)))

/- The equivalence evaluates on the identity-indexed summand in degree `k`. -/
#check SimplicialObject.copower.stdSimplex.homEquiv.apply (V := V) k X

end Full

section Truncated

variable {n k : ℕ} (hk : k ≤ n) (X : C)
variable (W : SimplicialObject.Truncated C n)
variable [HasCopower (Δ[k] : SSet.{w}) ((SimplicialObject.const C).obj X)]

/- The truncated bridge is the generic Yoneda calculation transported across an index
presheaf isomorphism. -/
#check Functor.indexedCoprod.uliftYoneda.homEquiv.ofIso

/- Lemma 14.13.4 (2): maps from the `n`-truncation of the full standard-simplex copower are
maps from `X` into degree `k` of an `n`-truncated target. -/
@[stacks 017F "Lemma 14.13.4 (2)"]
#check (SimplicialObject.copower.truncation.stdSimplex.homEquiv hk X W :
  ((SimplicialObject.truncation n).obj
      (SimplicialObject.copower (Δ[k] : SSet.{w})
        ((SimplicialObject.const C).obj X)) ⟶ W) ≃
    (X ⟶ W.obj (op ⦋k, hk⦌ₙ)))

/- The truncated equivalence has the same identity-simplex evaluation formula. -/
#check SimplicialObject.copower.truncation.stdSimplex.homEquiv.apply (W := W) hk X

end Truncated

end CategoryTheory
