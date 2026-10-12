/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting.BaseChange
import StacksCheckRecall

/-!
# Base change of formally smooth, étale, and unramified transformations

In a fibre product of transformations of functors on `(Sch/S)_fppf`, formal
smoothness, formal étaleness, and formal unramifiedness of `a : F ⟶ G` pass to
the base change `a' = pullback.fst b a`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme.Over

universe u v

/- Lemma 76.13.4 (1): If `a` is formally smooth, then the base change
`a' = pullback.fst b a` is formally smooth.
-/
@[stacks 049U]
#check (AlgebraicGeometry.Scheme.Over.FormallySmooth.pullback_fst :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) (b : H ⟶ G)
      [HasPullback b a] [FormallySmooth a], FormallySmooth (pullback.fst b a))

/- Lemma 76.13.4 (2): If `a` is formally étale, then the base change
`a' = pullback.fst b a` is formally étale.
-/
@[stacks 049U]
#check (AlgebraicGeometry.Scheme.Over.FormallyEtale.pullback_fst :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) (b : H ⟶ G)
      [HasPullback b a] [FormallyEtale a], FormallyEtale (pullback.fst b a))

/- Lemma 76.13.4 (3): If `a` is formally unramified, then the base change
`a' = pullback.fst b a` is formally unramified.
-/
@[stacks 049U]
#check (AlgebraicGeometry.Scheme.Over.FormallyUnramified.pullback_fst :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) (b : H ⟶ G)
      [HasPullback b a] [FormallyUnramified a],
      FormallyUnramified (pullback.fst b a))
