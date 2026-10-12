/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 37.75.2: A weighting of a locally quasi-finite morphism `f : X ⟶ Y`
is an integer-valued function on `X` whose fibre integrals are locally constant on
all finite open restrictions after étale base change. -/
@[stacks 0F3A] #check (AlgebraicGeometry.Scheme.Hom.IsWeighting :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.LocallyQuasiFinite f], (X → ℤ) → Prop)
