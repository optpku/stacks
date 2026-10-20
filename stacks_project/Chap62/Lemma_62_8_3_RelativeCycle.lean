/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Lemma_62_7_3_Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Effective
public import ReasLib.AlgebraicGeometry.RelativeCycle.EffectiveLocality

/-!
# Zariski locality of effective fibre cycle families

This file records the fibrewise effectiveness predicate on families of
`r`-cycles on scheme-theoretic fibres, together with the source-only and
target-only Zariski locality companions for effectiveness of relative
`r`-cycles.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom.CyclesOnFibers (restrict)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.IsEffective :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℤ}, CyclesOnFibers f r → Prop)

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.isEffective_iff :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℤ}
    (α : CyclesOnFibers f r),
    IsEffective α ↔
      ∀ s : S, ∀ x : f.fiber s, 0 ≤ α.toAlgebraicCycle s x)

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

namespace AlgebraicGeometry.RelativeCycle

#check (AlgebraicGeometry.RelativeCycle.isEffective_iff_of_source_iSup_eq_top :
  ∀
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : Family f r) (hα : IsRelative α) {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤),
    IsEffective α ↔
      ∀ i, IsEffective (restrict α (U i) ⊤ le_top))

#check (AlgebraicGeometry.RelativeCycle.isEffective_iff_of_target_iSup_eq_top :
  ∀
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : Family f r) (hα : IsRelative α) {κ : Type u}
    (V : κ → S.Opens) (hV : iSup V = ⊤),
    IsEffective α ↔
      ∀ j, IsEffective (restrict α (f ⁻¹ᵁ V j) (V j) le_rfl))

end AlgebraicGeometry.RelativeCycle
