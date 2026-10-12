/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.UniversalFiniteFree.SyntomicLocus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace UniversalFiniteFreeAlgebra

/- Lemma 49.11.3: there is an open subscheme `U_d ⊆ X_d` such that a morphism
`f : X ⟶ X_d` factors through `U_d` exactly when the base change
`Y_d ×_[X_d] X ⟶ X` of the universal finite locally free morphism is syntomic. -/
@[stacks 0FL0] #check
  (UniversalFiniteFreeAlgebra.exists_open_syntomicBaseChange_iff :
    ∀ d : ℕ+,
      ∃ U : (UniversalFiniteFreeAlgebra.baseScheme d).Opens,
        ∀ {X : Scheme.{0}}
          (f : X ⟶ UniversalFiniteFreeAlgebra.baseScheme d),
          (∃ g : X ⟶ U.toScheme, g ≫ U.ι = f) ↔
            Syntomic
              (pullback.snd (UniversalFiniteFreeAlgebra.projection d) f))

end UniversalFiniteFreeAlgebra
