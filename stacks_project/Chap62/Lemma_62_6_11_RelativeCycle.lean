module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Support
public import stacks_project.Chap62.Lemma_62_6_6_Relative

/-!
# Support of relative cycles

This file records the support of a family of fibrewise `r`-cycles, as the
union of the images of the fibrewise geometric supports in the total space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The support of a family of `r`-cycles on fibres of `f : X ⟶ S` is the union
over `s : S` of the images of `Supp(α_s) ⊂ X_s` in `X`. -/
def support {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} (α : Family f r) : Set X :=
  ⋃ s : S, f.fiberι s '' AlgebraicCycle.geometricSupport
    (CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s))

/-- The support of a fibrewise cycle family is the union of the images of the
fibrewise geometric supports along the fibre inclusions. -/
theorem support_def {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} (α : Family f r) :
    support α =
      ⋃ s : S, f.fiberι s '' AlgebraicCycle.geometricSupport
        (CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s)) :=
  sorry

/-- A point of `X` lies in the support of a fibrewise cycle family if and only if
it is the image of a point of the geometric support of the cycle on some
scheme-theoretic fibre. -/
theorem mem_support {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    (α : Family f r) (x : X) :
    x ∈ support α ↔
      ∃ (s : S) (y : f.fiber s),
        f.fiberι s y = x ∧
          y ∈ AlgebraicCycle.geometricSupport
            (CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s)) :=
  sorry

/-- Membership in the support of a fibrewise cycle family may be tested on the
unique scheme-theoretic fibre through the given point. -/
theorem mem_support_asFiber {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    (α : Family f r) (x : X) :
    x ∈ support α ↔
      f.asFiber x ∈ AlgebraicCycle.geometricSupport
        (CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (f x)) r (α (f x))) :=
  sorry

end AlgebraicGeometry.RelativeCycle
