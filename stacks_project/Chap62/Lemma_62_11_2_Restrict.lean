module

public import stacks_project.Chap62.Lemma_62_5_1_FiberMap
public import stacks_project.Chap62.Remark_62_5_6_Support_Family

/-!
# Restriction of fibre-cycle families along compatible opens

This file restricts a family of `r`-cycles on the fibres of `f : X ⟶ Y` to a
family on the fibres of `f.resLE V U hUV : U ⟶ V`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Function Set

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The fibre comparison of `f.resLE` built from `resLE_comp_ι` agrees with
`resLEFiberMap`. -/
theorem fiberMap_resLE_eq_resLEFiberMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (v : V.toScheme) :
    fiberMap (f.resLE V U hUV) U.ι V.ι f ⟨(resLE_comp_ι f hUV).symm⟩ v =
      resLEFiberMap f U V hUV v := sorry

namespace CyclesOnFibers

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {r : ℤ}

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

end CyclesOnFibers

end AlgebraicGeometry.Scheme.Hom
