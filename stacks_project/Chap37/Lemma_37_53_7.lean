/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.ConnectedComponents

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.53.7: for a flat proper finite-presentation morphism of schemes, the number of
geometric connected components of its fibres is lower semicontinuous on the base. -/
@[stacks 0BUI] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.lowerSemicontinuous_geometricFiberComponentCount :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.Flat f]
      [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.Scheme.Hom.FinitePresentation f],
      LowerSemicontinuous f.geometricFiberComponentCount)
