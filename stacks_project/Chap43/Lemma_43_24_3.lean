/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Moving

@[expose] public section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/- Lemma 43.24.3 -/
@[stacks 0B1U] #check (AlgebraicGeometry.CycleGroup.existsRationallyEquivalentIntersectProperly :
    ∀ (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.ProjectiveVariety X]
      [AlgebraicGeometry.Scheme.Regular X.left] (r s : ℤ)
      (α : AlgebraicGeometry.CycleGroup X.left
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
      (β : AlgebraicGeometry.CycleGroup X.left
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s),
      ∃ α' : AlgebraicGeometry.CycleGroup X.left
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r,
        AlgebraicGeometry.RationalEquivalence.RationallyEquivalent
            (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r α' α ∧
          AlgebraicGeometry.AlgebraicCycle.IntersectProperly
            (AlgebraicGeometry.CycleGroup.toAlgebraicCycle
              (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r α')
            (AlgebraicGeometry.CycleGroup.toAlgebraicCycle
              (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s β))
