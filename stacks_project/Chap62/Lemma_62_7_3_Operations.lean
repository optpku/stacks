module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import stacks_project.Chap62.Lemma_62_5_1_Operations
public import stacks_project.Chap62.Remark_62_5_6_Support_Family

/-!
# Bridges from fibre-cycle families to restriction, base change, and flat pullback

This file identifies the `CyclesOnFibers` restriction, base change, and flat
pullback maps with the existing `FiberCycleFamily` operations.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

variable {X S : Scheme.{u}}

/-- Restriction of a family of `r`-cycles on fibres to compatible opens
`U ⊆ X` and `V ⊆ S`, as the existing fibre-cycle restriction. -/
noncomputable def restrict {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (α : CyclesOnFibers f r) (U : X.Opens) (V : S.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    CyclesOnFibers (f.resLE V U hUV) r :=
  FiberCycleFamily.restrict U V hUV α

/-- Restriction of a fibre-cycle family is `FiberCycleFamily.restrict`. -/
theorem restrict_eq_fiberCycleFamilyRestrict {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} (α : CyclesOnFibers f r) (U : X.Opens)
    (V : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V) :
    restrict α U V hUV = FiberCycleFamily.restrict U V hUV α := sorry

/-- Base change of a family of `r`-cycles on fibres along `g : S' ⟶ S`, as
the existing fibre-cycle base change of the canonical pullback square. -/
noncomputable def baseChange {S' : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} (α : CyclesOnFibers f r) (g : S' ⟶ S) :
    CyclesOnFibers (pullback.snd f g) r :=
  FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α

/-- Base change of a fibre-cycle family is `FiberCycleFamily.baseChange` of the
canonical pullback square. -/
theorem baseChange_eq_fiberCycleFamilyBaseChange {S' : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} (α : CyclesOnFibers f r) (g : S' ⟶ S) :
    baseChange α g =
      FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α := sorry

/-- Flat pullback of a family of `r`-cycles on fibres along a flat morphism of
relative dimension `e`, as the existing fibre-cycle flat pullback. -/
noncomputable def flatPullback {X' : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} (α : CyclesOnFibers f r) (h : X' ⟶ X)
    (e : ℕ) [Flat h] [RelativeDimension h e] :
    CyclesOnFibers (h ≫ f) (r + e) :=
  FiberCycleFamily.flatPullback h rfl e α

/-- Flat pullback of a fibre-cycle family is `FiberCycleFamily.flatPullback`. -/
theorem flatPullback_eq_fiberCycleFamilyFlatPullback {X' : Scheme.{u}}
    {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ} (α : CyclesOnFibers f r)
    (h : X' ⟶ X) (e : ℕ) [Flat h] [RelativeDimension h e] :
    flatPullback α h e = FiberCycleFamily.flatPullback h rfl e α := sorry

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
