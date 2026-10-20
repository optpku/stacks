module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations

/-!
# Restriction of fibre-cycle families along compatible opens

A family of fibre cycles restricts coefficientwise to compatible open
subschemes of the source and target.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Function Set

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

namespace CyclesOnFibers

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyOfFiniteType f] {r : ℤ}

/-- Restricting fibre-cycle coefficients along the `resLE` fibre comparison has
locally finite support. -/
theorem restrict_locallyFiniteSupport (α : CyclesOnFibers f r)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (v : V.toScheme) :
    LocallyFiniteSupport fun x ↦
      toAlgebraicCycle α (V.ι v)
        (fiberMap (f.resLE V U hUV) U.ι V.ι f ⟨(resLE_comp_ι f hUV).symm⟩ v x) :=
  sorry

/-- The algebraic cycle on a restricted fibre obtained by taking coefficients
along the `resLE` fibre comparison. -/
noncomputable def restrictCycle (α : CyclesOnFibers f r)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (v : V.toScheme) :
    AlgebraicCycle ((f.resLE V U hUV).fiber v) ℤ where
  toFun := fun x ↦
    toAlgebraicCycle α (V.ι v)
      (fiberMap (f.resLE V U hUV) U.ι V.ι f ⟨(resLE_comp_ι f hUV).symm⟩ v x)
  supportWithinDomain' := subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    restrict_locallyFiniteSupport α U V hUV v x

/-- The restricted fibre cycle remains supported in dimension `r`. -/
theorem restrictCycle_mem_dimensionSubgroup (α : CyclesOnFibers f r)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (v : V.toScheme) :
    restrictCycle α U V hUV v ∈
      AlgebraicCycle.dimensionSubgroup
        ((f.resLE V U hUV).fiberCycleDimension v) r := sorry

/-- Restriction `α|_U` of a family of `r`-cycles on fibres of `X / Y` to
compatible opens `U ⊆ X` and `V ⊆ Y` with `f(U) ⊆ V`. -/
noncomputable def restrict (α : CyclesOnFibers f r) (U : X.Opens)
    (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) :
    CyclesOnFibers (f.resLE V U hUV) r :=
  fun v ↦
    ⟨restrictCycle α U V hUV v, restrictCycle_mem_dimensionSubgroup α U V hUV v⟩

/-- Coefficients of a restriction are the original coefficients at the compared
fibre point. -/
theorem restrict_apply (α : CyclesOnFibers f r) (U : X.Opens) (V : Y.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) (v : V.toScheme) (x : (f.resLE V U hUV).fiber v) :
    toAlgebraicCycle (restrict α U V hUV) v x =
      toAlgebraicCycle α (V.ι v)
        (fiberMap (f.resLE V U hUV) U.ι V.ι f ⟨(resLE_comp_ι f hUV).symm⟩ v x) :=
  sorry

/-- Restriction of a family of cycles on the fibres of `X / S` along an open of
`X`, as a family on the fibres of `U / S`. -/
noncomputable def restrictOver {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℤ} (α : CyclesOnFibers f r) (U : X.Opens) :
    CyclesOnFibers (U.ι ≫ f) r :=
  FiberCycleFamily.reindex (add_zero r)
    (FiberCycleFamily.flatPullback U.ι rfl 0 α)

/-- Coefficients of a total-space restriction are the original fibre
coefficients along the identity-triangle fibre map. -/
theorem restrictOver_apply {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℤ} (α : CyclesOnFibers f r) (U : X.Opens)
    (s : S) (x : (U.ι ≫ f).fiber s) :
    toAlgebraicCycle (restrictOver α U) s x =
      toAlgebraicCycle α s (idTriangleFiberMap U.ι rfl s x) := sorry

end CyclesOnFibers

end AlgebraicGeometry.Scheme.Hom
