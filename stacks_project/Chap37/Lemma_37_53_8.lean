/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.ConnectedComponents
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.53.8: for a proper, flat, finitely presented morphism with geometrically
reduced fibres, the geometric fibre component count is locally constant. -/
@[stacks 0E0N]
#check (AlgebraicGeometry.Scheme.Hom.FinitePresentation.isLocallyConstant_geometricFiberComponentCount :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.Flat f]
    [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.Scheme.Hom.FinitePresentation f]
    [AlgebraicGeometry.GeometricallyReduced f], IsLocallyConstant f.geometricFiberComponentCount)
