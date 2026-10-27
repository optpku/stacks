/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum

/-!
# Cycles of fixed dimension

This file provides the additive group of cycles of a fixed dimension, its locally finite sums,
and pushforward along quasicompact morphisms.
-/

@[expose] public section

open CategoryTheory Function Set Topology

noncomputable section

universe u v

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The additive group of algebraic cycles supported at points of dimension `k`. -/
abbrev CycleGroup (X : Scheme.{u}) (d : X → ℤ) (k : ℤ) : Type u :=
  AlgebraicCycle.dimensionSubgroup d k

namespace CycleGroup

/-- A degree-`k` cycle vanishes at every point whose dimension is not `k`. -/
theorem apply_eq_zero_of_dimension_ne (d : X → ℤ) (k : ℤ)
    (α : CycleGroup X d k) {x : X} (hx : d x ≠ k) : α.1 x = 0 := by
  by_contra h
  exact hx ((AlgebraicCycle.mem_dimensionSubgroup d k α.1).mp α.2 x h)

/-- Forget the dimension support condition on a cycle. -/
def toAlgebraicCycle (d : X → ℤ) (k : ℤ) :
    CycleGroup X d k →+ AlgebraicCycle X ℤ :=
  (AlgebraicCycle.dimensionSubgroup d k).subtype

/-- Forgetting the dimension support condition preserves every coefficient. -/
theorem toAlgebraicCycle_apply (d : X → ℤ) (k : ℤ)
    (α : CycleGroup X d k) (x : X) :
    toAlgebraicCycle d k α x = α.1 x := rfl

/-- Forgetting the dimension support condition is injective. -/
theorem toAlgebraicCycle_injective (d : X → ℤ) (k : ℤ) :
    Function.Injective (toAlgebraicCycle d k) := Subtype.val_injective

/-- The coefficientwise sum of degree-`k` cycles is again supported in degree `k`. -/
theorem locallyFiniteSum_mem_dimensionSubgroup {J : Type v} (d : X → ℤ) (k : ℤ)
    (c : J → CycleGroup X d k)
    (hc : LocallyFinite fun j ↦ (toAlgebraicCycle d k (c j)).support) :
    AlgebraicCycle.locallyFiniteSum (fun j ↦ toAlgebraicCycle d k (c j)) hc ∈
      AlgebraicCycle.dimensionSubgroup d k := by
  apply (AlgebraicCycle.mem_dimensionSubgroup d k _).mpr
  intro x hx
  by_contra h
  apply hx
  change (∑ᶠ j, toAlgebraicCycle d k (c j) x) = 0
  exact finsum_eq_zero_of_forall_eq_zero fun j ↦
    apply_eq_zero_of_dimension_ne d k (c j) h

/-- The coefficientwise sum of a locally finite family of degree-`k` cycles. -/
noncomputable def locallyFiniteSum {J : Type v} (d : X → ℤ) (k : ℤ)
    (c : J → CycleGroup X d k)
    (hc : LocallyFinite fun j ↦ (toAlgebraicCycle d k (c j)).support) :
    CycleGroup X d k :=
  ⟨AlgebraicCycle.locallyFiniteSum (fun j ↦ toAlgebraicCycle d k (c j)) hc,
    locallyFiniteSum_mem_dimensionSubgroup d k c hc⟩

/-- Evaluation of a locally finite sum is the corresponding pointwise finite sum. -/
theorem locallyFiniteSum_apply {J : Type v} (d : X → ℤ) (k : ℤ)
    (c : J → CycleGroup X d k)
    (hc : LocallyFinite fun j ↦ (toAlgebraicCycle d k (c j)).support) (x : X) :
    toAlgebraicCycle d k (locallyFiniteSum d k c hc) x =
      ∑ᶠ j, toAlgebraicCycle d k (c j) x := rfl

/-- Pushforward of a degree-`k` cycle is supported in degree `k` when the source and target
weights agree along every contributing point. -/
theorem map_mem_dimensionSubgroup (g : X ⟶ Y) [QuasiCompact g]
    (dX : X → ℤ) (dY : Y → ℤ) (k : ℤ) (c : CycleGroup X dX k) :
    AlgebraicCycle.map g dX dY (toAlgebraicCycle dX k c) ∈
      AlgebraicCycle.dimensionSubgroup dY k := by
  apply (AlgebraicCycle.mem_dimensionSubgroup dY k _).mpr
  intro y hy
  change (∑ᶠ x ∈ g.base ⁻¹' {y},
    c.1 x * (AlgebraicCycle.mapCoeff g dX dY x : ℤ)) ≠ 0 at hy
  obtain ⟨x, hx, hcoeff⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  have hxk : dX x = k :=
    (AlgebraicCycle.mem_dimensionSubgroup dX k c.1).mp c.2 x (left_ne_zero_of_mul hcoeff)
  have hw : dX x = dY (g.base x) := by
    by_contra h
    simp [AlgebraicCycle.mapCoeff, h] at hcoeff
  have hxy : g.base x = y := hx
  simpa only [hxy] using hw.symm.trans hxk

/-- The underlying value of pushforward on degree-`k` cycles. -/
noncomputable def mapValue (g : X ⟶ Y) [QuasiCompact g]
    (dX : X → ℤ) (dY : Y → ℤ) (k : ℤ) (c : CycleGroup X dX k) :
    CycleGroup Y dY k :=
  ⟨AlgebraicCycle.map g dX dY (toAlgebraicCycle dX k c),
    map_mem_dimensionSubgroup g dX dY k c⟩

/-- Pushforward sends the zero degree-`k` cycle to zero. -/
theorem mapValue_zero (g : X ⟶ Y) [QuasiCompact g]
    (dX : X → ℤ) (dY : Y → ℤ) (k : ℤ) :
    mapValue g dX dY k 0 = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  change AlgebraicCycle.map g dX dY (0 : AlgebraicCycle X ℤ) y = 0
  simp [AlgebraicCycle.map]

/-- Pushforward preserves addition of degree-`k` cycles. -/
theorem mapValue_add (g : X ⟶ Y) [QuasiCompact g]
    (dX : X → ℤ) (dY : Y → ℤ) (k : ℤ) (a b : CycleGroup X dX k) :
    mapValue g dX dY k (a + b) = mapValue g dX dY k a + mapValue g dX dY k b := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  have hfinite (c : AlgebraicCycle X ℤ) :
      (g.base ⁻¹' {y} ∩
        Function.support (fun x ↦ c x * (AlgebraicCycle.mapCoeff g dX dY x : ℤ))).Finite := by
    obtain ⟨U, hU, hyU, _⟩ :=
      (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
        (mem_univ y) isOpen_univ
    have hcompact : IsCompact (g.base ⁻¹' U) :=
      g.isSpectralMap.isCompact_preimage_of_isOpen hU.1 hU.2
    refine (c.locallyFiniteSupport.finite_inter_support_of_isCompact hcompact).subset ?_
    rintro x ⟨hx, hcx⟩
    refine ⟨?_, left_ne_zero_of_mul hcx⟩
    change g.base x ∈ U
    have hxy : g.base x = y := hx
    rw [hxy]
    exact hyU
  change AlgebraicCycle.map g dX dY (a.1 + b.1) y =
    AlgebraicCycle.map g dX dY a.1 y + AlgebraicCycle.map g dX dY b.1 y
  simp only [AlgebraicCycle.map, Function.locallyFinsupp.map_apply,
    Function.locallyFinsuppWithin.coe_add, Pi.add_apply, add_mul]
  exact finsum_mem_add_distrib' (hfinite a.1) (hfinite b.1)

/-- Pushforward of degree-`k` cycles along a quasicompact scheme morphism. -/
noncomputable def mapHom (g : X ⟶ Y) [QuasiCompact g]
    (dX : X → ℤ) (dY : Y → ℤ) (k : ℤ) :
    CycleGroup X dX k →+ CycleGroup Y dY k where
  toFun := mapValue g dX dY k
  map_zero' := mapValue_zero g dX dY k
  map_add' := mapValue_add g dX dY k

/-- Coefficients of the pushforward homomorphism are computed by `AlgebraicCycle.map`. -/
theorem mapHom_apply (g : X ⟶ Y) [QuasiCompact g]
    (dX : X → ℤ) (dY : Y → ℤ) (k : ℤ) (c : CycleGroup X dX k) (y : Y) :
    toAlgebraicCycle dY k (mapHom g dX dY k c) y =
      AlgebraicCycle.map g dX dY (toAlgebraicCycle dX k c) y := rfl

/-- Pushforward along the identity morphism is the identity on degree-`k` cycles. -/
theorem mapHom_id (d : X → ℤ) (k : ℤ) :
    mapHom (𝟙 X) d d k = AddMonoidHom.id (CycleGroup X d k) := by
  apply AddMonoidHom.ext
  intro c
  apply Subtype.ext
  exact AlgebraicCycle.map_id d c.1

end CycleGroup

end AlgebraicGeometry
