/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normal.FiberCriterion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.20.2: A scheme morphism with locally Noetherian fibres is normal if
and only if it is flat and its fibres are geometrically normal. -/
@[stacks 0391] #check
  (AlgebraicGeometry.normal_iff_flat_and_geometricallyNormal :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      (_ : AlgebraicGeometry.LocallyNoetherianFibers f),
      AlgebraicGeometry.Normal f ↔ AlgebraicGeometry.Flat f ∧
        AlgebraicGeometry.geometrically AlgebraicGeometry.Scheme.isNormal f)
