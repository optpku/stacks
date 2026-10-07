module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.SeparableClosure
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import stacks_project.Chap62.Lemma_62_6_6_Family

/-!
# Weightings attached to fibrewise 0-cycles

This file constructs the integer map `w_α` sending a point `x` of `X` to the
coefficient of `x` in the fibrewise 0-cycle `α_{f(x)}`, multiplied by the
finite inseparable degree of `κ(x)` over `κ(f(x))`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The integer map attached to a family of fibrewise 0-cycles, sending `x` to
the coefficient of `f.asFiber x` in `α (f x)`, multiplied by the finite
inseparable degree of `κ(x)` over `κ(f x)`. -/
noncomputable def weighting {X S : Scheme.{u}} {f : X ⟶ S} (α : Family f 0) :
    X → ℤ :=
  fun x ↦
    CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (f x)) 0 (α (f x))
        (f.asFiber x) *
      (Field.finInsepDegree (S.residueField (f x)) (X.residueField x) : ℤ)

/-- The value of `weighting α` at `x` is the fibrewise coefficient of `x` times
the finite inseparable residue-field degree. -/
theorem weighting_apply {X S : Scheme.{u}} {f : X ⟶ S} (α : Family f 0) (x : X) :
    weighting α x =
      CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (f x)) 0 (α (f x))
          (f.asFiber x) *
        (Field.finInsepDegree (S.residueField (f x)) (X.residueField x) : ℤ) :=
  sorry

end AlgebraicGeometry.RelativeCycle
