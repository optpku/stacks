module

public import ReasLib.Topology.KrullDimension.Equidimensional
public import stacks_project.Chap109.Lemma_109_8_1_Substack

/-!
# The object property of Cohen–Macaulay families of curves of relative dimension 1

`𝒞urves^{CM, 1}` is the full subcategory of families of curves whose structure
morphism is Cohen–Macaulay of relative dimension 1. Membership is the
source-facing packaging of a classifying morphism factoring through that open
substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The object property of Cohen–Macaulay families of curves of relative
dimension 1, corresponding to the open substack `𝒞urves^{CM, 1}`. -/
def cohenMacaulayDim1 (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.CohenMacaulay (hom P) ∧ RelativeDimension (hom P) 1

/-- Membership in `cohenMacaulayDim1` is Cohen–Macaulayness of the structure
morphism together with exact relative dimension 1. -/
theorem cohenMacaulayDim1_iff {S : Scheme.{u}} (P : Obj S) :
    cohenMacaulayDim1 S P ↔
      AlgebraicSpace.CohenMacaulay (hom P) ∧ RelativeDimension (hom P) 1 :=
  sorry

/-- The Cohen–Macaulay relative-dimension-1 property of families of curves is
closed under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_cohenMacaulayDim1 (S : Scheme.{u}) :
    (cohenMacaulayDim1 S).IsClosedUnderIsomorphisms :=
  sorry

/-- Membership in `𝒞urves^{CM, 1}` implies membership in `𝒞urves^{CM}`. -/
theorem cohenMacaulayDim1_le_cohenMacaulay {S : Scheme.{u}} (P : Obj S) :
    cohenMacaulayDim1 S P → cohenMacaulay S P :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
