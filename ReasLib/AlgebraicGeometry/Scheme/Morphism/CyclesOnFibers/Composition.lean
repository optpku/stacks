module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations

/-!
# Composition of families of cycles on fibres

Composition is defined fibrewise by the cap action after base change to an
intermediate fibre.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/-- Base change of a family of `r`-cycles on fibres of `X / Y` along
`Y_s ⟶ Y`, as a family on fibres of `X_s / Y_s`. -/
noncomputable def baseChangeFiberι {X Y S : Scheme.{u}} {f : X ⟶ Y}
    (p : Y ⟶ S) [LocallyOfFiniteType f] {r : ℤ} (α : CyclesOnFibers f r)
    (s : S) : CyclesOnFibers (compFiberToBaseFiber f p s) r :=
  FiberCycleFamily.baseChange (isPullback_compFiberToBaseFiber f p s) α

/-- Composition of families of degrees `r` and `e` on fibres of `X / Y`
and `Y / S`. Its value at `s` is the cap of the base change of the first
family to `Y_s` with the second family's value at `s`. -/
noncomputable def comp {X Y S : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℤ}
    (α : CyclesOnFibers f r) (β : CyclesOnFibers p e) :
    CyclesOnFibers (f ≫ p) (r + e) :=
  fun s ↦
    cast (congrArg (fun d ↦ CycleGroup ((f ≫ p).fiber s) d (r + e))
      (relativeDimensionFunction_congr
        (compFiberToBaseFiber_fiberToSpecResidueField f p s) (fun _ ↦ 0)))
      (cap (p.fiberToSpecResidueField s) (compFiberToBaseFiber f p s) (fun _ ↦ 0)
        (baseChangeFiberι p α s) (β s))

/-- Forgetting the grading of a composite family at `s` gives the fibrewise
cap of the base change of the first family with the second fibre cycle. -/
theorem comp_apply {X Y S : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℤ}
    (α : CyclesOnFibers f r) (β : CyclesOnFibers p e) (s : S) :
    CycleGroup.toAlgebraicCycle ((f ≫ p).fiberCycleDimension s) (r + e)
        (comp α β s) =
      CycleGroup.toAlgebraicCycle
        ((compFiberToBaseFiber f p s ≫ p.fiberToSpecResidueField s).relativeDimensionFunction
          (fun _ ↦ 0)) (r + e)
        (cap (p.fiberToSpecResidueField s) (compFiberToBaseFiber f p s) (fun _ ↦ 0)
          (baseChangeFiberι p α s) (β s)) := sorry

/-- Composition with the zero family on fibres of `X / Y` is zero. -/
theorem comp_zero_left {X Y S : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℤ}
    (β : CyclesOnFibers p e) :
    comp (0 : CyclesOnFibers f r) β = 0 := sorry

/-- Composition with the zero family on fibres of `Y / S` is zero. -/
theorem comp_zero_right {X Y S : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℤ}
    (α : CyclesOnFibers f r) :
    comp α (0 : CyclesOnFibers p e) = 0 := sorry

/-- Composition of families of cycles on fibres is additive in its first family. -/
theorem comp_add_left {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℤ}
    (α₁ α₂ : CyclesOnFibers f r) (β : CyclesOnFibers p e) :
    comp (α₁ + α₂) β = comp α₁ β + comp α₂ β := sorry

/-- Composition of families of cycles on fibres is additive in its second family. -/
theorem comp_add_right {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℤ}
    (α : CyclesOnFibers f r) (β₁ β₂ : CyclesOnFibers p e) :
    comp α (β₁ + β₂) = comp α β₁ + comp α β₂ := sorry

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
