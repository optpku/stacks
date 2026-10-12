/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.CycleGroup
public import stacks_project.Chap62.Definition_62_6_1_Specialization
public import stacks_project.Chap62.Lemma_62_5_1_FiberMap

/-!
# Restriction of relative cycles to an open of the source

This file restricts families of fibrewise `r`-cycles, and the group `z(X/S, r)`,
along an open of the source over the same base, landing in `z(U/S, r)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Function Set

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The fibrewise bound `dim(X_s \ U_s) < r`. -/
def fiberOpenComplementDimensionLT {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (r : ℕ) : Prop :=
  ∀ s : S, topologicalKrullDim {x : f.fiber s // x ∉ f.fiberOpen U s} <
    (r : WithBot ℕ∞)

/-- The fibrewise bound is the source condition `dim(X_s \ U_s) < r`. -/
theorem fiberOpenComplementDimensionLT_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (r : ℕ) :
    fiberOpenComplementDimensionLT f U r ↔
      ∀ s : S,
        topologicalKrullDim {x : f.fiber s // f.fiberι s x ∉ U} <
          (r : WithBot ℕ∞) := sorry

/-- Restricting fibre-cycle coefficients along `idTriangleFiberMap` of `U.ι`
has locally finite support. -/
theorem restrictOpen_locallyFiniteSupport {X S : Scheme.{u}} {f : X ⟶ S}
    {r : ℕ} (U : X.Opens) (α : Family f r) (s : S) :
    LocallyFiniteSupport fun x : (U.ι ≫ f).fiber s ↦
      CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s)
        (Scheme.Hom.idTriangleFiberMap U.ι rfl s x) := sorry

/-- The algebraic cycle on a fibre of `U.ι ≫ f` obtained by restricting
coefficients along `idTriangleFiberMap`. -/
noncomputable def restrictOpenCycle {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    (U : X.Opens) (α : Family f r) (s : S) :
    AlgebraicCycle ((U.ι ≫ f).fiber s) ℤ where
  toFun := fun x ↦
    CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s)
      (Scheme.Hom.idTriangleFiberMap U.ι rfl s x)
  supportWithinDomain' := subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    restrictOpen_locallyFiniteSupport U α s x

/-- The restricted fibre cycle remains supported in dimension `r`. -/
theorem restrictOpenCycle_mem_dimensionSubgroup {X S : Scheme.{u}}
    {f : X ⟶ S} {r : ℕ} (U : X.Opens) (α : Family f r) (s : S) :
    restrictOpenCycle U α s ∈
      AlgebraicCycle.dimensionSubgroup ((U.ι ≫ f).fiberDimensionFunction s)
        r := sorry

/-- Restriction of a family of fibrewise `r`-cycles to an open of the source
over the same base. This is the source operation `α|_U` landing on fibres of
`U.ι ≫ f`. -/
noncomputable def restrictOpen {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    (U : X.Opens) (α : Family f r) : Family (U.ι ≫ f) r :=
  fun s ↦
    ⟨restrictOpenCycle U α s, restrictOpenCycle_mem_dimensionSubgroup U α s⟩

/-- Coefficients of `restrictOpen` are the original fibre coefficients along
`idTriangleFiberMap`. -/
theorem restrictOpen_apply {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    (U : X.Opens) (α : Family f r) (s : S) (x : (U.ι ≫ f).fiber s) :
    CycleGroup.toAlgebraicCycle ((U.ι ≫ f).fiberDimensionFunction s) r
        (restrictOpen U α s) x =
      CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s)
        (Scheme.Hom.idTriangleFiberMap U.ι rfl s x) := sorry

/-- Restriction to an open of the source preserves the relative-cycle
condition. -/
theorem isRelative_restrictOpen {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (U : X.Opens)
    [LocallyOfFiniteType (U.ι ≫ f)] {r : ℕ} {α : Family f r}
    (hα : IsRelative α) : IsRelative (restrictOpen U α) := sorry

/-- The restriction of an element of `z(X/S, r)` lies in `z(U/S, r)`. -/
theorem groupRestrict_mem {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (U : X.Opens)
    [LocallyOfFiniteType (U.ι ≫ f)] (r : ℕ) (α : group f r) :
    restrictOpen U (α : Family f r) ∈ group (U.ι ≫ f) r := sorry

/-- Restriction of relative `r`-cycles to an open of the source over `S`. -/
noncomputable def groupRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (U : X.Opens)
    [LocallyOfFiniteType (U.ι ≫ f)] (r : ℕ) :
    group f r →+ group (U.ι ≫ f) r where
  toFun α :=
    ⟨restrictOpen U (α : Family f r), groupRestrict_mem f U r α⟩
  map_zero' := sorry
  map_add' := sorry

/-- The underlying fibrewise family of `groupRestrict` is family-level
restriction. -/
theorem groupRestrict_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (U : X.Opens)
    [LocallyOfFiniteType (U.ι ≫ f)] (r : ℕ) (α : group f r) :
    (groupRestrict f U r α : Family (U.ι ≫ f) r) =
      restrictOpen U (α : Family f r) := sorry

/-- Restriction of families of `r`-cycles on fibres to an open of the source is
a bijection when the complement is fibrewise of dimension less than `r`. -/
theorem restrictOpen_bijective {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] (U : X.Opens) {r : ℕ}
    (hdim : fiberOpenComplementDimensionLT f U r) :
    Function.Bijective (fun α : Family f r ↦ restrictOpen U α) := sorry

end AlgebraicGeometry.RelativeCycle

