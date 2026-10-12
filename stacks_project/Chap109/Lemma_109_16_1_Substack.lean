/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap109.Lemma_109_8_1_Substack

/-!
# The object properties of smooth families of curves

`𝒞urves^{smooth}` and `𝒞urves^{smooth, 1}` are the full subcategories of
families of curves whose structure morphisms are smooth, respectively smooth of
relative dimension 1. Membership is the source-facing packaging of a classifying
morphism factoring through those open substacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The object property of smooth families of curves, corresponding to the
open substack 𝒞urves^{smooth}. -/
def smooth (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.Smooth (hom P)

/-- Membership in `smooth` is smoothness of the structure morphism. -/
theorem smooth_iff {S : Scheme.{u}} (P : Obj S) :
    smooth S P ↔ AlgebraicSpace.Smooth (hom P) :=
  sorry

/-- The smoothness property of families of curves is closed under
isomorphisms. -/
instance instIsClosedUnderIsomorphisms_smooth (S : Scheme.{u}) :
    (smooth S).IsClosedUnderIsomorphisms :=
  sorry

/-- The object property of smooth families of curves of relative dimension 1,
corresponding to the open substack `𝒞urves^{smooth, 1}`. -/
def smoothDim1 (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1

/-- Membership in `smoothDim1` is smoothness of the structure morphism together
with exact relative dimension 1. -/
theorem smoothDim1_iff {S : Scheme.{u}} (P : Obj S) :
    smoothDim1 S P ↔
      AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1 :=
  sorry

/-- The smoothness relative-dimension-1 property of families of curves is
closed under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_smoothDim1 (S : Scheme.{u}) :
    (smoothDim1 S).IsClosedUnderIsomorphisms :=
  sorry

/-- Membership in `𝒞urves^{smooth, 1}` implies membership in `𝒞urves^{smooth}`. -/
theorem smoothDim1_le_smooth {S : Scheme.{u}} (P : Obj S) :
    smoothDim1 S P → smooth S P :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
