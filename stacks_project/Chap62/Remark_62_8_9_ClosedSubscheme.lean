module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import stacks_project.Chap62.Example_62_5_4_AssociatedCycle
public import stacks_project.Chap62.Lemma_62_6_6_Family

/-!
# Fibre cycles of closed subschemes

This file evaluates the associated `r`-cycle of a closed subscheme on a
scheme-theoretic fibre, as a class of the relative fibre-cycle group.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The associated `r`-cycle `[Z_s]_r` of the inverse image of a closed
subscheme in the scheme-theoretic fibre over `s`. -/
noncomputable def closedSubschemeFiber {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (Z : X.IdealSheafData) (r : ℕ)
    (hZ : f.fiberClosedSubschemeDimensionLE Z r) (s : S) :
    f.fiberCycleGroup s r :=
  f.closedSubschemeFiberCycleFamily Z r hZ s

/-- The fibre associated cycle is the closed-subscheme cycle of the inverse
image of `Z` in `X_s`. -/
theorem closedSubschemeFiber_spec {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (Z : X.IdealSheafData) (r : ℕ)
    (hZ : f.fiberClosedSubschemeDimensionLE Z r) (s : S) :
    closedSubschemeFiber f Z r hZ s =
      (f.fiberToSpecResidueField s).closedSubschemeCycle (fun _ ↦ (0 : ℤ))
        (f.fiberClosedSubscheme Z s) (r : ℤ)
        (f.fiberClosedSubschemeDeltaDimension_le_of_topologicalKrullDim_le Z r (hZ s)) :=
  sorry

end AlgebraicGeometry.RelativeCycle
