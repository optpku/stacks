/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.EtaleNeighborhood
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 37.53.3: the fibre of a scheme morphism over a point is geometrically connected
if and only if every pointed étale neighbourhood gives a connected base-changed fibre. -/
@[stacks 03GZ] #check
  (AlgebraicGeometry.GeometricallyConnected.iff_connectedSpace_etaleNeighborhood :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (s : S),
      GeometricallyConnected (f.fiberToSpecResidueField s) ↔
        ∀ U : Scheme.EtaleNeighborhood S s,
          ConnectedSpace ((pullback.snd f U.toEtale.hom).fiber U.point))
