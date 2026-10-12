/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.9.5: a locally finite type morphism `f : X ⟶ S`, with `X` quasi-compact and
quasi-separated and `S` quasi-separated, presents `X` as a directed limit of quasi-compact,
quasi-separated schemes of finite presentation over `S`; all transition morphisms and all
projections from `X` are closed immersions. -/
@[stacks 09ZQ] #check
  (AlgebraicGeometry.Scheme.Limit.IsClosedImmersionFinitePresentationApproximation.exists_of_locallyOfFiniteType :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace S],
      ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
        ∃ (_ : IsDirected I (· ≤ ·)), ∃ (D : OrderDual I ⥤ Scheme.{u}),
          ∃ (π : (Functor.const (OrderDual I)).obj X ⟶ D),
            ∃ (σ : ∀ j : I, D.obj j ⟶ S),
              AlgebraicGeometry.Scheme.Limit.IsClosedImmersionFinitePresentationApproximation
                f D π σ)
