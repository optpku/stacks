module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers

/-!
# Action of fibre-cycle families on cycles

The action of a family of `r`-cycles on the fibres of `X / Y` sends
degree-`e` cycles of `Y` to degree-`r + e` cycles of `X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Function Set

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/-- The coefficient of `cap p f δ α β` at a point `x` of `X` is the product of
the coefficient of `β` at `f x` and the coefficient of the fibre cycle
`α (f x)` at `f.asFiber x`. -/
noncomputable def capCoeff {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    (δ : S → ℤ) {r e : ℤ} (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e) (x : X) : ℤ :=
  CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) e β (f x) *
    toAlgebraicCycle α (f x) (f.asFiber x)

/-- The coefficient function of the fibre-cycle action has locally finite
support. -/
theorem capCoeff_locallyFiniteSupport {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ] {r e : ℤ}
    (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e) :
    LocallyFiniteSupport (capCoeff p f δ α β) := sorry

/-- The underlying algebraic cycle of the fibre-cycle action. -/
noncomputable def capCycle {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ] {r e : ℤ}
    (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e) :
    AlgebraicCycle X ℤ where
  toFun := capCoeff p f δ α β
  supportWithinDomain' := subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    capCoeff_locallyFiniteSupport p f δ α β x

/-- The fibre-cycle action is supported in relative dimension `r + e`. -/
theorem cap_mem_dimensionSubgroup {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ] {r e : ℤ}
    (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e) :
    capCycle p f δ α β ∈
      AlgebraicCycle.dimensionSubgroup
        ((f ≫ p).relativeDimensionFunction δ) (r + e) := sorry

/-- The action of a family of `r`-cycles on the fibres of `f : X ⟶ Y` on a
degree-`e` cycle of `Y`, valued in degree `r + e` cycles of `X`. -/
noncomputable def cap {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ] {r e : ℤ}
    (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e) :
    CycleGroup X ((f ≫ p).relativeDimensionFunction δ) (r + e) :=
  ⟨capCycle p f δ α β, cap_mem_dimensionSubgroup p f δ α β⟩

/-- Forgetting the dimension grading of a fibre-cycle action recovers the
coefficientwise product `capCoeff`. -/
theorem cap_apply {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ] {r e : ℤ}
    (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e) (x : X) :
    CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ) (r + e)
        (cap p f δ α β) x =
      capCoeff p f δ α β x := sorry

/-- The fibre-cycle action of the zero family is the zero cycle. -/
theorem cap_zero_left {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ] {r e : ℤ}
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e) :
    cap p f δ (0 : CyclesOnFibers f r) β = 0 := sorry

/-- The fibre-cycle action on the zero cycle is zero. -/
theorem cap_zero_right {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ] {r : ℤ}
    (α : CyclesOnFibers f r) (e : ℤ) :
    cap p f δ α (0 : CycleGroup Y (p.relativeDimensionFunction δ) e) = 0 := sorry

/-- The fibre-cycle action is additive in the family of fibre cycles. -/
@[stacks 0H66]
theorem cap_add_left {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ] {r e : ℤ}
    (α₁ α₂ : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e) :
    cap p f δ (α₁ + α₂) β = cap p f δ α₁ β + cap p f δ α₂ β := sorry

/-- The fibre-cycle action is additive in the cycle on the base. -/
@[stacks 0H66]
theorem cap_add_right {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ] {r e : ℤ}
    (α : CyclesOnFibers f r)
    (β₁ β₂ : CycleGroup Y (p.relativeDimensionFunction δ) e) :
    cap p f δ α (β₁ + β₂) = cap p f δ α β₁ + cap p f δ α β₂ := sorry

/-- The fibre-cycle action of a fixed family, as an additive homomorphism in the
cycle of `Y`. -/
noncomputable def capHom {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ] {r : ℤ}
    (α : CyclesOnFibers f r) (e : ℤ) :
    CycleGroup Y (p.relativeDimensionFunction δ) e →+
      CycleGroup X ((f ≫ p).relativeDimensionFunction δ) (r + e) where
  toFun := cap p f δ α
  map_zero' := cap_zero_right p f δ α e
  map_add' := cap_add_right p f δ α

/-- Evaluating the additive homomorphism of a fibre-cycle action recovers `cap`. -/
theorem capHom_apply {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ] {r : ℤ}
    (α : CyclesOnFibers f r) (e : ℤ)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e) :
    capHom p f δ α e β = cap p f δ α β := sorry

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
