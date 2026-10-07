module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Support

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The dimension function on a scheme-theoretic fibre is relative dimension over
the residue field, with the zero dimension function on its spectrum. -/
noncomputable abbrev fiberCycleDimension {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    f.fiber s → ℤ :=
  (f.fiberToSpecResidueField s).relativeDimensionFunction (fun _ ↦ 0)

/-- The fibrewise cycle dimension is relative dimension over the residue field
with zero dimension function on its spectrum. -/
theorem fiberCycleDimension_apply {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (x : f.fiber s) :
    fiberCycleDimension f s x =
      (f.fiberToSpecResidueField s).relativeDimensionFunction (fun _ ↦ 0) x := sorry

/-- A family of `r`-cycles on the scheme-theoretic fibres of `f : X ⟶ S`. -/
abbrev CyclesOnFibers {X S : Scheme.{u}} (f : X ⟶ S) (r : ℤ) : Type u :=
  (s : S) → CycleGroup (f.fiber s) (f.fiberCycleDimension s) r

namespace CyclesOnFibers

/-- Forget the dimension grading of a fibre cycle, yielding an algebraic cycle
on that scheme-theoretic fibre. -/
def toAlgebraicCycle {X S : Scheme.{u}} {f : X ⟶ S} {r : ℤ}
    (α : CyclesOnFibers f r) (s : S) : AlgebraicCycle (f.fiber s) ℤ :=
  CycleGroup.toAlgebraicCycle (f.fiberCycleDimension s) r (α s)

/-- Forgetting the fibrewise dimension grading preserves coefficients. -/
theorem toAlgebraicCycle_apply {X S : Scheme.{u}} {f : X ⟶ S} {r : ℤ}
    (α : CyclesOnFibers f r) (s : S) (x : f.fiber s) :
    toAlgebraicCycle α s x =
      CycleGroup.toAlgebraicCycle (f.fiberCycleDimension s) r (α s) x := sorry

/-- The support of a family of fibre cycles is the union of the images of the
fibrewise geometric supports under the fibre inclusions. -/
def support {X S : Scheme.{u}} {f : X ⟶ S} {r : ℤ} (α : CyclesOnFibers f r) :
    Set X :=
  ⋃ s : S, f.fiberι s '' AlgebraicCycle.geometricSupport (α.toAlgebraicCycle s)

/-- The support of a family of fibre cycles is the union of the images of the
fibrewise geometric supports along the fibre inclusions. -/
theorem support_def {X S : Scheme.{u}} {f : X ⟶ S} {r : ℤ}
    (α : CyclesOnFibers f r) :
    support α =
      ⋃ s : S, f.fiberι s '' AlgebraicCycle.geometricSupport (α.toAlgebraicCycle s) := sorry

/-- A point lies in the support of a family of fibre cycles if and only if it is
the image of a point in the geometric support of the cycle on some fibre. -/
theorem mem_support {X S : Scheme.{u}} {f : X ⟶ S} {r : ℤ}
    (α : CyclesOnFibers f r) (x : X) :
    x ∈ support α ↔
      ∃ (s : S) (y : f.fiber s),
        f.fiberι s y = x ∧
          y ∈ AlgebraicCycle.geometricSupport (α.toAlgebraicCycle s) := sorry

/-- Membership in the support of a family of fibre cycles may be tested on the
unique scheme-theoretic fibre through the given point. -/
theorem mem_support_asFiber {X S : Scheme.{u}} {f : X ⟶ S} {r : ℤ}
    (α : CyclesOnFibers f r) (x : X) :
    x ∈ support α ↔
      f.asFiber x ∈ AlgebraicCycle.geometricSupport (α.toAlgebraicCycle (f x)) := sorry

end CyclesOnFibers

end AlgebraicGeometry.Scheme.Hom
