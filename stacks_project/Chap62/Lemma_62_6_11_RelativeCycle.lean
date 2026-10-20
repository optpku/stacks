/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers
public import stacks_project.Chap62.Lemma_62_6_6_Relative

/-!
# Support of relative cycles

This file records the support of a family of fibrewise `r`-cycles, as the
union of the images of the fibrewise geometric supports in the total space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The support of a family of `r`-cycles on fibres of `f : X ⟶ S` is the union
over `s : S` of the images of `Supp(α_s) ⊂ X_s` in `X`. -/
abbrev support {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ} (α : Family f r) : Set X :=
  Scheme.Hom.CyclesOnFibers.support α

/- The support is the union of the images of the fibrewise geometric supports. -/
#check (Scheme.Hom.CyclesOnFibers.support_def :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ} (α : Family f r), support α =
      ⋃ s : S, f.fiberι s '' AlgebraicCycle.geometricSupport
        (CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s)))

/- Support membership is witnessed by a point in a fibrewise geometric support. -/
#check (Scheme.Hom.CyclesOnFibers.mem_support :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ} (α : Family f r) (x : X),
    x ∈ support α ↔
      ∃ (s : S) (y : f.fiber s),
        f.fiberι s y = x ∧
          y ∈ AlgebraicCycle.geometricSupport
            (CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s)))

/- Support membership can be tested in the fibre through the given point. -/
#check (Scheme.Hom.CyclesOnFibers.mem_support_asFiber :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ} (α : Family f r) (x : X),
    x ∈ support α ↔
      f.asFiber x ∈ AlgebraicCycle.geometricSupport
        (CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (f x)) r (α (f x))))

end AlgebraicGeometry.RelativeCycle
