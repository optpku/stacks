/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Noetherian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure

universe u

/- Lemma 75.13.7 (1): over a Noetherian algebraic space, an object of `D_QCoh(𝒪_X)` is
`m`-pseudo-coherent exactly when it is bounded above and its cohomology sheaves in degrees
`i ≥ m` are coherent. -/
@[stacks 08IK] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.isMPseudoCoherent_iff_boundedAbove_and_cohomology_coherent_ge :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X] (E : DerivedQCoh X) (m : ℤ),
      IsMPseudoCoherent X E.obj m ↔
        (t.minus : ObjectProperty (ModuleDerived X)) E.obj ∧
          ∀ i : ℤ, m ≤ i →
            ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj).IsCoherent)

/- Lemma 75.13.7 (2): over a Noetherian algebraic space, an object of `D_QCoh(𝒪_X)` is
pseudo-coherent exactly when it is bounded above and has coherent cohomology in every degree. -/
@[stacks 08IK] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.isPseudoCoherent_iff_boundedAbove_and_cohomology_coherent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X] (E : DerivedQCoh X),
      IsPseudoCoherent X E.obj ↔
        (t.minus : ObjectProperty (ModuleDerived X)) E.obj ∧
          DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent (structureSheaf X)) E.obj)
