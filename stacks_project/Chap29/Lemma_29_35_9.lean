/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.35.9 (1): an unramified morphism is locally of finite type. -/
@[stacks 02GD] #check
  (@AlgebraicGeometry.Unramified.toLocallyOfFiniteType :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.Unramified f → AlgebraicGeometry.LocallyOfFiniteType f)

/- Lemma 29.35.9 (2): a G-unramified morphism is locally of finite presentation. -/
@[stacks 02GD] #check
  (@AlgebraicGeometry.GUnramified.toLocallyOfFinitePresentation :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.GUnramified f → AlgebraicGeometry.LocallyOfFinitePresentation f)
