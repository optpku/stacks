/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.ProperSupport
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Theorem 30.27.1 (Grothendieck's existence theorem) -/
@[stacks 088E] #check
  (AlgebraicGeometry.Scheme.Modules.instIsEquivalence_coherentProperSupportCompletionFunctor :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {X : Scheme.{u}} [IsNoetherian X] (I : Ideal A) [IsAdicComplete I A]
      (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [Scheme.Hom.FiniteType f],
      (AlgebraicGeometry.Scheme.Modules.coherentProperSupportCompletionFunctor :
        AlgebraicGeometry.Scheme.Modules.CoherentProperSupportOver f ⥤
          AlgebraicGeometry.Scheme.Modules.CoherentFormalProperSupportOver f
            ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec I).comap f)).IsEquivalence)
