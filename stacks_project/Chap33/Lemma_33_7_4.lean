/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.ConnectedComponents
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.7.4: if `X` and `Y` are schemes over a field `k` and `X` is geometrically connected
over `k`, then the second projection `X ×[Spec k] Y ⟶ Y` induces a bijection on connected
components. -/
@[stacks 0385] #check
  (AlgebraicGeometry.GeometricallyConnected.pullbackSndConnectedComponentsMap_bijective :
    ∀ {k : Type u} [Field k] {X Y : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      (g : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      [AlgebraicGeometry.GeometricallyConnected f],
      Function.Bijective
        (((CategoryTheory.Limits.pullback.snd f g).continuous.connectedComponentsMap) :
          ConnectedComponents
              (CategoryTheory.Limits.pullback f g : AlgebraicGeometry.Scheme.{u}) →
            ConnectedComponents Y))
