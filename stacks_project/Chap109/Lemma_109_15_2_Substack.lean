/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Definition_76_48_1_LocalCompleteIntersection
public import stacks_project.Chap109.Lemma_109_7_3_Substack
public import stacks_project.Chap109.Lemma_109_14_1_Substack

/-!
# The object property of lci families of curves with isolated singularities

`𝒞urves^{lci+}` is the full subcategory of families of curves that are local
complete intersections and have isolated singularities. Membership is the
source-facing packaging of a classifying morphism factoring through that open
substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The object property of local complete intersection families of curves with
isolated singularities, corresponding to the open substack `𝒞urves^{lci+}`. -/
def lciPlus (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.IsLocalCompleteIntersection (hom P) ∧
    IsolatedSingularities (hom P)

/-- Membership in `lciPlus` is local complete intersection of the structure
morphism together with isolated singularities. -/
theorem lciPlus_iff {S : Scheme.{u}} (P : Obj S) :
    lciPlus S P ↔
      AlgebraicSpace.IsLocalCompleteIntersection (hom P) ∧
        IsolatedSingularities (hom P) :=
  sorry

/-- The `lciPlus` property of families of curves is closed under
isomorphisms. -/
instance instIsClosedUnderIsomorphisms_lciPlus (S : Scheme.{u}) :
    (lciPlus S).IsClosedUnderIsomorphisms :=
  sorry

/-- Membership in `𝒞urves^{lci+}` implies that the structure morphism is a
local complete intersection. -/
theorem lciPlus_isLocalCompleteIntersection {S : Scheme.{u}} {P : Obj S}
    (h : lciPlus S P) : AlgebraicSpace.IsLocalCompleteIntersection (hom P) :=
  sorry

/-- Membership in `𝒞urves^{lci+}` implies isolated singularities of the
structure morphism. -/
theorem lciPlus_isolatedSingularities {S : Scheme.{u}} {P : Obj S}
    (h : lciPlus S P) : IsolatedSingularities (hom P) :=
  sorry

/-- The full subcategory of `𝒞urves` cut out by `lciPlus` is fibred in
groupoids over `Over S`. -/
instance instIsFiberedInGroupoids_lciPlus (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((lciPlus S).ι ⋙ p S) :=
  sorry

/-- The inclusion of `𝒞urves^{lci+}` into `𝒞urves` is an open immersion. -/
instance instOpenImmersion_inclusionOf_lciPlus (S : Scheme.{u}) :
    CohStack.Hom.OpenImmersion (inclusionOf (lciPlus S)) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
