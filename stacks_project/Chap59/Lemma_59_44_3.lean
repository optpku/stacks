/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AlmostCocontinuous
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- Lemma 59.44.3: if every étale base change of `f : X ⟶ Y` has Property (C)
and is closed, then pullback from the small étale site of `Y` to that of `X` is
almost cocontinuous. -/
@[stacks 04DV] #check
  (AlgebraicGeometry.Scheme.smallEtalePullback_isAlmostCocontinuous :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      (∀ V : Y.Etale,
        AlgebraicGeometry.Scheme.Etale.SmallToBig.hasPropertyC
          (pullback.snd f V.hom)) →
      (∀ V : Y.Etale, IsClosedMap (pullback.snd f V.hom).base) →
      Functor.IsAlmostCocontinuous (Scheme.smallEtalePullback f)
        Y.smallEtaleTopology X.smallEtaleTopology)
