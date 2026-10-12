/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.6.8 (1): a scheme morphism is unramified if and only if it is formally
unramified and locally of finite type. -/
@[stacks 02HE] #check
  (AlgebraicGeometry.unramified_iff_formallyUnramified_and_locallyOfFiniteType :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Unramified f ↔
        AlgebraicGeometry.FormallyUnramified f ∧ AlgebraicGeometry.LocallyOfFiniteType f)

/- Lemma 37.6.8 (2): a scheme morphism is G-unramified if and only if it is formally
unramified and locally of finite presentation. -/
@[stacks 02HE] #check
  (AlgebraicGeometry.gUnramified_iff_formallyUnramified_and_locallyOfFinitePresentation :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.GUnramified f ↔
        AlgebraicGeometry.FormallyUnramified f ∧
          AlgebraicGeometry.LocallyOfFinitePresentation f)
