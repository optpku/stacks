/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Principal
public import stacks_project.Chap67.Lemma_67_23_5
public import stacks_project.Chap72.Definition_72_6_9_Principal
public import stacks_project.Chap72.Lemma_72_7_3_Quotient
public import stacks_project.Chap82.Definition_82_2_5_DeltaDimension
public import stacks_project.Chap82.Definition_82_17_1_Cycle

/-!
# Principal divisor cycles on good integral algebraic spaces

A rational unit on a good integral algebraic space determines an `(n-1)`-cycle
by converting the principal Weil divisor of Spaces over Fields, Definition
72.6.7, into a locally finite cycle on `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 82.13.1: A rational unit on a good integral algebraic space of
`δ`-dimension `n` determines its principal divisor as an `(n - 1)`-cycle. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.principalDivisor :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
      [QuasiSeparated f] [LocallyOfFiniteType f] [IsIntegral X]
      (δ : Points B → ℤ) [IsDimensionFunction δ] (n : ℤ),
      Hom.deltaDimension f δ (univIrreducibleClosed X) = n →
        (RationalFunction X)ˣ → Hom.cycleGroup f δ (n - 1))
