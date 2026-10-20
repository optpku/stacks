/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Colimit.Representable.Counterexamples.RankCollapse
import StacksCheckRecall

@[expose] public section

/-!
# Collapsed Initial Segments and Representable Colimits

The rank-collapse system and its generic noninjectivity criterion are owned by ReasLib. This file
records their specialization to the natural-number system of the source example.
-/

open CategoryTheory Opposite

namespace CategoryTheory.Limits.Types.RankCollapse.Nat

/- Example 19.2.2 (05NQ): the colimit of the natural-number rank-collapse system is a
one-point type. -/
@[stacks 05NQ "one-point colimit"] #check
  (colimitEquivPUnit (id : ℕ → ℕ) 0 :
    colimit (diagram (id : ℕ → ℕ)) ≃ PUnit)

/- Example 19.2.2 (05NQ): the natural-number projection and zero-constant maps remain distinct
in the represented-Hom colimit. -/
@[stacks 05NQ "distinct projection and constant classes"] #check
  (projectionClass_ne_zeroConstant :
    ∀ n : ℕ,
      colimit.ι (diagram (id : ℕ → ℕ) ⋙ coyoneda.obj (op ℕ)) n
          (projection (id : ℕ → ℕ) n) ≠
        colimit.ι (diagram (id : ℕ → ℕ) ⋙ coyoneda.obj (op ℕ)) n
          (baseConstant (id : ℕ → ℕ) 0 n))

/- Example 19.2.2 (05NQ): those classes have the same image under the representable-colimit
comparison. -/
@[stacks 05NQ "equal projection and constant images"] #check
  (comparison_projection_eq_zeroConstant :
    ∀ n : ℕ,
      colimit.post (diagram (id : ℕ → ℕ)) (coyoneda.obj (op ℕ))
          (colimit.ι (diagram (id : ℕ → ℕ) ⋙ coyoneda.obj (op ℕ)) n
            (projection (id : ℕ → ℕ) n)) =
        colimit.post (diagram (id : ℕ → ℕ)) (coyoneda.obj (op ℕ))
          (colimit.ι (diagram (id : ℕ → ℕ) ⋙ coyoneda.obj (op ℕ)) n
            (baseConstant (id : ℕ → ℕ) 0 n)))

/- Example 19.2.2 (05NQ): hence the representable-colimit comparison for the natural-number
rank-collapse system is not injective. -/
@[stacks 05NQ "representable comparison not injective"] #check
  (comparison_not_injective :
    ¬ Function.Injective
      (colimit.post (diagram (id : ℕ → ℕ)) (coyoneda.obj (op ℕ))))

end CategoryTheory.Limits.Types.RankCollapse.Nat
