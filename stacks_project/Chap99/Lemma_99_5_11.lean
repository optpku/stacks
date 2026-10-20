/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.OpennessOfVersality

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open TopologicalSpace

universe u

/- Lemma 99.5.11: for a flat morphism of finite presentation to a locally
Noetherian scheme, the stack of coherent sheaves satisfies openness of versality. -/
@[stacks 08WA] #check
  (AlgebraicGeometry.AlgebraicSpace.CohStack.opennessOfVersality :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : AlgebraicSpace S} (f : X ⟶ ofOver (Over.mk (𝟙 S)))
    [FinitePresentation f] [Flat f] {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj f) (hx : (p f).obj x = Over.mk hU)
    (u0 : U), IsFiniteTypePoint u0 → IsVersalAt f hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt f hU x hx u)
