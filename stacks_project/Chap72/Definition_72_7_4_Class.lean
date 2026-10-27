/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.MeromorphicSection.ClassGroup
public import stacks_project.Chap72.Lemma_72_7_3_Quotient

/-!
# Weil divisor classes of invertible modules

The class of an invertible module is computed from any of its regular
meromorphic sections. The rational-quotient API remains available here.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace CategoryTheory.MonoidalCategory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.invertibleModuleWeilDivisorClass_eq :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X] (L : X.Modules) [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s),
    invertibleModuleWeilDivisorClass L =
      nonzeroMeromorphicSectionWeilDivisorClass s hs)
