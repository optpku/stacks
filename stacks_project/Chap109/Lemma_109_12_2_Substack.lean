/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap109.Lemma_109_12_1_Substack

/-!
# The object property of Gorenstein families of curves of relative dimension 1

`𝒞urves^{Gorenstein, 1}` is the full subcategory of families of curves whose
structure morphism is Gorenstein of relative dimension 1. Membership is the
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

/-- The object property of Gorenstein families of curves of relative
dimension 1, corresponding to the open substack `𝒞urves^{Gorenstein, 1}`. -/
def gorensteinDim1 (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.Gorenstein (hom P) ∧ RelativeDimension (hom P) 1

/-- Membership in `gorensteinDim1` is Gorensteinness of the structure
morphism together with exact relative dimension 1. -/
theorem gorensteinDim1_iff {S : Scheme.{u}} (P : Obj S) :
    gorensteinDim1 S P ↔
      AlgebraicSpace.Gorenstein (hom P) ∧ RelativeDimension (hom P) 1 :=
  sorry

/-- The Gorenstein relative-dimension-1 property of families of curves is
closed under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_gorensteinDim1 (S : Scheme.{u}) :
    (gorensteinDim1 S).IsClosedUnderIsomorphisms :=
  sorry

/-- Membership in `𝒞urves^{Gorenstein, 1}` implies membership in
`𝒞urves^{Gorenstein}`. -/
theorem gorensteinDim1_le_gorenstein {S : Scheme.{u}} (P : Obj S) :
    gorensteinDim1 S P → gorenstein S P :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
