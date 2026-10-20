/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.ProperSupport
import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Proper
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

/- Remark 30.27.2 (Unwinding Grothendieck's existence theorem): coherent formal modules encode
the pushed-forward coherent modules on the infinitesimal thickenings through annihilation by powers
of `I` and successor quotient compatibility, with the first stage carrying the support condition.
The special proper case omits that support restriction. -/
@[stacks 088F] #check
  (@AlgebraicGeometry.Scheme.Modules.instIsEquivalence_coherentProperSupportCompletionFunctor :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {X : Scheme.{u}} [IsNoetherian X]
      (I : Ideal A) [IsAdicComplete I A]
      (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [Scheme.Hom.FiniteType f],
      (AlgebraicGeometry.Scheme.Modules.coherentProperSupportCompletionFunctor :
        AlgebraicGeometry.Scheme.Modules.CoherentProperSupportOver f ⥤
          AlgebraicGeometry.Scheme.Modules.CoherentFormalProperSupportOver f
            ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec I).comap f)).IsEquivalence)

#check
  (@AlgebraicGeometry.Scheme.CoherentCompletion.functor_isEquivalence_of_isProper :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {X : Scheme.{u}} [IsNoetherian X]
      (I : Ideal A) [IsAdicComplete I A]
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f],
      (AlgebraicGeometry.Scheme.CoherentCompletion.functor
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec I).comap f)).IsEquivalence)

