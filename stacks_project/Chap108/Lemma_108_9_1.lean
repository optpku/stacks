/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Gerbe
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.9.1: the canonical morphism makes the Picard stack a gerbe over
its relative Picard functor under the section hypotheses. -/
@[stacks 0DME] #check (AlgebraicGeometry.AlgebraicSpace.Picard.toFunctor_isGerbeMorphism :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Flat f] [Proper f] [FinitePresentation f]
    [Hom.IsIsoBaseChangeStructurePushforward f],
    CartesianBasedFunctor.IsGerbeMorphism (SchemesOver.fppfTopology B) (Picard.toFunctor f))
