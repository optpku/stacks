/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
    (α : CycleGroup X d k) {x : X} (hx : d x ≠ k) : α.1 x = 0 := sorry

/-- Forget the dimension support condition on a cycle. -/
def toAlgebraicCycle (d : X → ℤ) (k : ℤ) :
    CycleGroup X d k →+ AlgebraicCycle X ℤ :=
  (AlgebraicCycle.dimensionSubgroup d k).subtype

/-- Forgetting the dimension support condition preserves every coefficient. -/
theorem toAlgebraicCycle_apply (d : X → ℤ) (k : ℤ)
    (α : CycleGroup X d k) (x : X) :
    toAlgebraicCycle d k α x = α.1 x := sorry

/-- Forgetting the dimension support condition is injective. -/
theorem toAlgebraicCycle_injective (d : X → ℤ) (k : ℤ) :
    Function.Injective (toAlgebraicCycle d k) := sorry

/-- The coefficientwise sum of degree-`k` cycles is again supported in degree `k`. -/
theorem locallyFiniteSum_mem_dimensionSubgroup {J : Type v} (d : X → ℤ) (k : ℤ)
    (c : J → CycleGroup X d k)
    (hc : LocallyFinite fun j ↦ (toAlgebraicCycle d k (c j)).support) :
    AlgebraicCycle.locallyFiniteSum (fun j ↦ toAlgebraicCycle d k (c j)) hc ∈
      AlgebraicCycle.dimensionSubgroup d k := sorry

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
      ∑ᶠ j, toAlgebraicCycle d k (c j) x := sorry

/-- Pushforward of a degree-`k` cycle is supported in degree `k` when the source and target
weights agree along every contributing point. -/
theorem map_mem_dimensionSubgroup (g : X ⟶ Y) [QuasiCompact g]
    (dX : X → ℤ) (dY : Y → ℤ) (k : ℤ) (c : CycleGroup X dX k) :
    AlgebraicCycle.map g dX dY (toAlgebraicCycle dX k c) ∈
      AlgebraicCycle.dimensionSubgroup dY k := sorry

/-- The underlying value of pushforward on degree-`k` cycles. -/
noncomputable def mapValue (g : X ⟶ Y) [QuasiCompact g]
    (dX : X → ℤ) (dY : Y → ℤ) (k : ℤ) (c : CycleGroup X dX k) :
    CycleGroup Y dY k :=
  ⟨AlgebraicCycle.map g dX dY (toAlgebraicCycle dX k c),
    map_mem_dimensionSubgroup g dX dY k c⟩

/-- Pushforward sends the zero degree-`k` cycle to zero. -/
theorem mapValue_zero (g : X ⟶ Y) [QuasiCompact g]
    (dX : X → ℤ) (dY : Y → ℤ) (k : ℤ) :
    mapValue g dX dY k 0 = 0 := sorry

/-- Pushforward preserves addition of degree-`k` cycles. -/
theorem mapValue_add (g : X ⟶ Y) [QuasiCompact g]
    (dX : X → ℤ) (dY : Y → ℤ) (k : ℤ) (a b : CycleGroup X dX k) :
    mapValue g dX dY k (a + b) = mapValue g dX dY k a + mapValue g dX dY k b := sorry

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
      AlgebraicCycle.map g dX dY (toAlgebraicCycle dX k c) y := sorry

/-- Pushforward along the identity morphism is the identity on degree-`k` cycles. -/
theorem mapHom_id (d : X → ℤ) (k : ℤ) :
    mapHom (𝟙 X) d d k = AddMonoidHom.id (CycleGroup X d k) := sorry

end CycleGroup

end AlgebraicGeometry
