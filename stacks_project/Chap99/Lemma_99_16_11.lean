/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.FormalEffectiveness

/-!
# Lemma 99.16.11

In Situation 99.16.3, if `B = S` is locally Noetherian, then strong formal
effectiveness in the sense of Artin's Axioms, Remark 98.20.2 holds for
`p : Complexes f ⥤ Over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Complexes

universe u

/- Lemma 99.16.11: in Situation 99.16.3, if `B = S` is locally Noetherian,
then every compatible system of objects of `Complexes f` over spectra of a
sequential inverse system of algebras with surjective locally nilpotent
transitions is effective over the spectrum of the inverse limit. -/
@[stacks 0DLM] #check
  (AlgebraicGeometry.AlgebraicSpace.Complexes.strongFormalEffectiveness :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : AlgebraicSpace S}
      (f : X ⟶ ofOver (Over.mk (𝟙 S))) [Proper f] [Flat f] [FinitePresentation f]
      (ξ : FormalObjectSystem (p f)), ξ.IsEffective)
