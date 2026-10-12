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

/- Lemma 37.28.6: for a finitely presented morphism of schemes, each finite
level set of the geometric connected-fibre component count is locally constructible. -/
@[stacks 055I] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.geometricFiberComponentCount_levelSet_isLocallyConstructible :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation f] (n : ℕ),
      Topology.IsLocallyConstructible {y : Y | f.geometricFiberComponentCount y = n})
