module

import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Proper
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.13.2: let `f : X ⟶ S` be a proper morphism with `S` quasi-compact and
quasi-separated. Then `X` is a directed limit of schemes `X_i` proper and of finite presentation
over `S`, such that all transition morphisms and all projections `X ⟶ X_i` are closed
immersions. -/
@[stacks 09ZR] #check
  (AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.exists_of_isProper :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
      [CompactSpace S] [QuasiSeparatedSpace S],
      ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
        ∃ (_ : IsDirected I (· ≤ ·)), ∃ (D : OrderDual I ⥤ Scheme.{u}),
          ∃ (π : (Functor.const (OrderDual I)).obj X ⟶ D),
            ∃ (σ : ∀ j : I, D.obj j ⟶ S),
              AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.IsProperClosedImmersion
                f D π σ)
