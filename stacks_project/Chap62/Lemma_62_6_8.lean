module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Union
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.InDimensions
public import stacks_project.Chap62.Definition_62_6_1_Specialization
public import stacks_project.Chap62.Example_62_5_4_AssociatedCycle

/-!
# Associated closed-subscheme families as relative cycles

This file records that the fibrewise associated-cycle family of a closed
subscheme is a relative cycle when the closed subscheme is flat over the base
in sufficiently large dimensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The closed subscheme `Z ⊂ X` is flat over `S` in dimensions `≥ r` when the
pushed-forward structure sheaf `(Z ⟶ X)_* O_Z` is flat over `S` in dimensions
`≥ r`. -/
def closedSubschemeFlatOverInDimensionsGE {X S : Scheme.{u}} (f : X ⟶ S)
    (Z : X.IdealSheafData) (r : ℕ) : Prop :=
  Modules.flatOverInDimensionsGE (closedSubschemeStructureSheafOn Z) f r

/-- Flatness of `Z` over `S` in dimensions `≥ r` is the module-theoretic
condition on `(Z ⟶ X)_* O_Z`. -/
theorem closedSubschemeFlatOverInDimensionsGE_iff {X S : Scheme.{u}}
    (f : X ⟶ S) (Z : X.IdealSheafData) (r : ℕ) :
    f.closedSubschemeFlatOverInDimensionsGE Z r ↔
      Modules.flatOverInDimensionsGE (closedSubschemeStructureSheafOn Z) f r := sorry

/-- If `Z ⟶ S` is flat, then `Z` is flat over `S` in dimensions `≥ r`. -/
theorem closedSubschemeFlatOverInDimensionsGE_of_flat {X S : Scheme.{u}}
    (f : X ⟶ S) (Z : X.IdealSheafData) (r : ℕ)
    (hflat : Flat (Z.subschemeι ≫ f)) :
    f.closedSubschemeFlatOverInDimensionsGE Z r := sorry

/-- Lemma 62.6.8: in the situation of Example 62.5.4, if `S` is locally Noetherian
and `Z` is flat over `S` in dimensions `≥ r`, then the associated fibrewise
family `closedSubschemeFiberCycleFamily f Z r hZ` is a relative `r`-cycle on
`X / S`. -/
@[stacks 0H57]
theorem closedSubschemeFiberCycleFamily_isRelative {X S : Scheme.{u}}
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (Z : X.IdealSheafData) (r : ℕ)
    (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (hflat : f.closedSubschemeFlatOverInDimensionsGE Z r) :
    RelativeCycle.IsRelative (closedSubschemeFiberCycleFamily f Z r hZ) := sorry

/-- The associated fibrewise family of a closed subscheme that is flat over `S`
in dimensions `≥ r` lies in the group `z(X/S, r)` of relative `r`-cycles. -/
theorem closedSubschemeFiberCycleFamily_mem_group {X S : Scheme.{u}}
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (Z : X.IdealSheafData) (r : ℕ)
    (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (hflat : f.closedSubschemeFlatOverInDimensionsGE Z r) :
    closedSubschemeFiberCycleFamily f Z r hZ ∈ RelativeCycle.group f r := sorry

end AlgebraicGeometry.Scheme.Hom
