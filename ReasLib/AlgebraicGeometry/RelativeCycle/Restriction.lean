/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.RelativeCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Comparison

/-!
# Restriction of relative cycles to an open of the source

Families of fibre cycles and relative cycles restrict to an open over the same
base. Restriction is bijective when each fibre complement has dimension less
than the degree of the cycles.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Function Set

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Every complement of the fibre open has Krull dimension strictly less than `r`. -/
def fiberOpenComplementDimensionLT {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (r : ℕ) : Prop :=
  ∀ s : S, topologicalKrullDim {x : f.fiber s // x ∉ f.fiberOpen U s} <
    (r : WithBot ℕ∞)

/-- The fibre-complement dimension bound can be expressed using the inverse image
of the open under the fibre inclusion. -/
theorem fiberOpenComplementDimensionLT_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (r : ℕ) :
    fiberOpenComplementDimensionLT f U r ↔
      ∀ s : S,
        topologicalKrullDim {x : f.fiber s // f.fiberι s x ∉ U} <
          (r : WithBot ℕ∞) := sorry

/-- Restricting fibre-cycle coefficients along the comparison map of an open
immersion has locally finite support. -/
theorem restrictOpen_locallyFiniteSupport {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} (U : X.Opens) (α : f.FiberCycleFamily r) (s : S) :
    LocallyFiniteSupport fun x : (U.ι ≫ f).fiber s ↦
      CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s)
        (Scheme.Hom.idTriangleFiberMap U.ι rfl s x) := sorry

/-- The algebraic cycle on a fibre of the open restriction obtained by pulling
back coefficients along the fibre comparison map. -/
noncomputable def restrictOpenCycle {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    [LocallyOfFiniteType f] (U : X.Opens) (α : f.FiberCycleFamily r) (s : S) :
    AlgebraicCycle ((U.ι ≫ f).fiber s) ℤ where
  toFun := fun x ↦
    CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s)
      (Scheme.Hom.idTriangleFiberMap U.ι rfl s x)
  supportWithinDomain' := subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    restrictOpen_locallyFiniteSupport U α s x

/-- The restriction of a fibre cycle of dimension `r` is supported in dimension `r`. -/
theorem restrictOpenCycle_mem_dimensionSubgroup {X S : Scheme.{u}}
    {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (U : X.Opens) (α : f.FiberCycleFamily r) (s : S) :
    restrictOpenCycle U α s ∈
      AlgebraicCycle.dimensionSubgroup ((U.ι ≫ f).fiberDimensionFunction s)
        r := sorry

/-- Restriction of a family of fibrewise `r`-cycles to an open of the source
over the same base. -/
noncomputable def restrictOpen {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    [LocallyOfFiniteType f] (U : X.Opens) (α : f.FiberCycleFamily r) :
    (U.ι ≫ f).FiberCycleFamily r :=
  fun s ↦
    ⟨restrictOpenCycle U α s, restrictOpenCycle_mem_dimensionSubgroup U α s⟩

/-- Coefficients of the restricted family are the original fibre coefficients
evaluated along the fibre comparison map. -/
theorem restrictOpen_apply {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    [LocallyOfFiniteType f] (U : X.Opens) (α : f.FiberCycleFamily r)
    (s : S) (x : (U.ι ≫ f).fiber s) :
    CycleGroup.toAlgebraicCycle ((U.ι ≫ f).fiberDimensionFunction s) r
        (restrictOpen U α s) x =
      CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s)
        (Scheme.Hom.idTriangleFiberMap U.ι rfl s x) := sorry

/-- Restriction to an open of the source preserves compatibility with
specialization after every discrete valuation ring base change. -/
theorem isRelative_restrictOpen {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (U : X.Opens)
    {r : ℕ} {α : f.FiberCycleFamily r}
    (hα : IsRelative α) : IsRelative (restrictOpen U α) := sorry

/-- The restriction of a relative `r`-cycle belongs to the relative-cycle
subgroup of the open restriction. -/
theorem groupRestrict_mem {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (U : X.Opens)
    (r : ℕ) (α : group f r) :
    restrictOpen U (α : f.FiberCycleFamily r) ∈ group (U.ι ≫ f) r := sorry

/-- Restriction of the zero family of fibre cycles is the zero family. -/
theorem restrictOpen_zero {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    [LocallyOfFiniteType f] (U : X.Opens) :
    restrictOpen U (0 : f.FiberCycleFamily r) = 0 := sorry

/-- Restriction of families of fibre cycles preserves addition. -/
theorem restrictOpen_add {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    [LocallyOfFiniteType f] (U : X.Opens) (α β : f.FiberCycleFamily r) :
    restrictOpen U (α + β) = restrictOpen U α + restrictOpen U β := sorry

/-- The additive homomorphism restricting relative `r`-cycles to an open of
the source over the same base. -/
noncomputable def groupRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (U : X.Opens) (r : ℕ) :
    group f r →+ group (U.ι ≫ f) r where
  toFun α :=
    ⟨restrictOpen U (α : f.FiberCycleFamily r), groupRestrict_mem f U r α⟩
  map_zero' := Subtype.ext (restrictOpen_zero U)
  map_add' := fun α β ↦
    Subtype.ext (restrictOpen_add U (α : f.FiberCycleFamily r) (β : f.FiberCycleFamily r))

/-- The underlying fibrewise family of the relative-cycle restriction
homomorphism is the restriction of the underlying family. -/
theorem groupRestrict_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (U : X.Opens)
    (r : ℕ) (α : group f r) :
    (groupRestrict f U r α : (U.ι ≫ f).FiberCycleFamily r) =
      restrictOpen U (α : f.FiberCycleFamily r) := sorry

/-- Restriction of families of `r`-cycles on fibres is bijective when every
fibre complement has dimension strictly less than `r`. -/
theorem restrictOpen_bijective {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] (U : X.Opens) {r : ℕ}
    (hdim : fiberOpenComplementDimensionLT f U r) :
    Function.Bijective (fun α : f.FiberCycleFamily r ↦ restrictOpen U α) := sorry

/-- For a locally finite type morphism over a locally Noetherian base,
restriction of relative `r`-cycles to an open is bijective if every fibre
complement has dimension strictly less than `r`. -/
theorem groupRestrict_bijective {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (U : X.Opens) (r : ℕ)
    (hdim : fiberOpenComplementDimensionLT f U r) :
    Function.Bijective (groupRestrict f U r) := sorry

end AlgebraicGeometry.RelativeCycle
