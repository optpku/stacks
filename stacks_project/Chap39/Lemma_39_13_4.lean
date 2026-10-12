/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 39.13.4 (1): The square formed by the two projections from the scheme of
composable arrows and the source and target maps is cartesian. -/
@[stacks 02YE] #check
  (AlgebraicGeometry.GroupoidScheme.fstSndIsPullback :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
      IsPullback (pullback.fst G.s G.t) (pullback.snd G.s G.t) G.s G.t)

/- Lemma 39.13.4 (2): The square formed by composition, the second projection, and
two copies of the source map is cartesian. -/
@[stacks 02YE] #check
  (AlgebraicGeometry.GroupoidScheme.compSndIsPullback :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
      IsPullback G.c (pullback.snd G.s G.t) G.s G.s)

/- Lemma 39.13.4 (3): The square formed by the first projection, composition, and
two copies of the target map is cartesian. -/
@[stacks 02YE] #check
  (AlgebraicGeometry.GroupoidScheme.fstCompIsPullback :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
      IsPullback (pullback.fst G.s G.t) G.c G.t G.t)

end AlgebraicGeometry.GroupoidScheme
