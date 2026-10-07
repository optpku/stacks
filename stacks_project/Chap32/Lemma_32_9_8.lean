module

import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Finite
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.9.8: let `f : X ⟶ S` be a finite morphism with `S` quasi-compact and
quasi-separated. Then `X` is a directed limit of schemes finite and of finite presentation over
`S`, with closed-immersion transition maps. -/
@[stacks 09YY] #check
  (AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.exists_of_isFinite :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
      [CompactSpace S] [QuasiSeparatedSpace S],
      ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
        ∃ (_ : IsDirected I (· ≤ ·)), ∃ (D : OrderDual I ⥤ Scheme.{u}),
          ∃ (π : (Functor.const (OrderDual I)).obj X ⟶ D),
            ∃ (σ : ∀ j : I, D.obj j ⟶ S),
              AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.IsFiniteClosedImmersion
                f D π σ)
