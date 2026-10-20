module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Topology.Defs.Induced
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap109.Lemma_109_15_2_Substack
public import stacks_project.Chap109.Lemma_109_17_1_Points

/-!
# Inclusion of smooth curves into lci-plus curves

The object property of smooth families of curves is contained in the lci-plus
property. The induced 1-morphism of full subcategories of `𝒞urves` is an open
immersion, and the image of `CohStack.Points.map` is the source-facing subset
`|𝒞urves^{smooth}| ⊂ |𝒞urves^{lci+}|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of smooth families of curves, corresponding to the open
substack `𝒞urves^{smooth}`. -/
def smooth (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.Smooth (hom P)

/-- Membership in `smooth` is smoothness of the structure morphism. -/
theorem smooth_iff {S : Scheme.{u}} (P : Obj S) :
    smooth S P ↔ AlgebraicSpace.Smooth (hom P) :=
  sorry

/-- Membership in `smooth` implies membership in `lciPlus`. -/
theorem smooth_le_lciPlus (S : Scheme.{u}) : smooth S ≤ lciPlus S := sorry

/-- The full subcategory of `𝒞urves` cut out by `smooth` is fibred in groupoids
over `Over S`. -/
instance instIsFiberedInGroupoids_smooth (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((smooth S).ι ⋙ p S) :=
  sorry

/-- The full subcategory of `𝒞urves` cut out by `smooth` is an algebraic stack in
the Hom-universe of `CohStack.toGroupoids`. -/
instance instAlgebraicStack_ofObjectProperty_smooth (S : Scheme.{u}) :
    CohStack.AlgebraicStack (ofObjectProperty (smooth S)) :=
  sorry

/-- The full subcategory of `𝒞urves` cut out by `lciPlus` is an algebraic stack in
the Hom-universe of `CohStack.toGroupoids`. -/
instance instAlgebraicStack_ofObjectProperty_lciPlus (S : Scheme.{u}) :
    CohStack.AlgebraicStack (ofObjectProperty (lciPlus S)) :=
  sorry

/-- The inclusion of `𝒞urves^{smooth}` into `𝒞urves` is an open immersion. -/
instance instOpenImmersion_inclusionOf_smooth (S : Scheme.{u}) :
    CohStack.Hom.OpenImmersion (inclusionOf (smooth S)) :=
  sorry

/-- The inclusion of `𝒞urves^{smooth}` into `𝒞urves^{lci+}`, as a 1-morphism of
categories fibred in groupoids over `Over S`. -/
def inclusionSmoothLciPlus (S : Scheme.{u}) :
    ofObjectProperty (smooth S) ⟶ ofObjectProperty (lciPlus S) :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    { toFunctor := ιOfLE (smooth_le_lciPlus S)
      w := sorry }

/-- The underlying functor of `inclusionSmoothLciPlus S` is the identity-on-carriers
map of `smooth_le_lciPlus`. -/
theorem inclusionSmoothLciPlus_toFunctor (S : Scheme.{u}) :
    FiberedCategoryOver.Groupoids.toFunctor (inclusionSmoothLciPlus S) =
      ιOfLE (smooth_le_lciPlus S) :=
  sorry

/-- The inclusion of `𝒞urves^{smooth}` into `𝒞urves^{lci+}` is an open immersion. -/
instance instOpenImmersion_inclusionSmoothLciPlus (S : Scheme.{u}) :
    CohStack.Hom.OpenImmersion (inclusionSmoothLciPlus S) :=
  sorry

/-- The set of points of `𝒞urves^{lci+}` in the image of
`|𝒞urves^{smooth}| → |𝒞urves^{lci+}|`. -/
def smoothPointsSet (S : Scheme.{u}) :
    Set (CohStack.Points (ofObjectProperty (lciPlus S))) :=
  Set.range (CohStack.Points.map (inclusionSmoothLciPlus S))

/-- `smoothPointsSet S` is the range of `CohStack.Points.map` of
`inclusionSmoothLciPlus S`. -/
theorem smoothPointsSet_eq (S : Scheme.{u}) :
    smoothPointsSet S =
      Set.range (CohStack.Points.map (inclusionSmoothLciPlus S)) :=
  sorry

/-- A point of `|𝒞urves^{lci+}|` lies in `smoothPointsSet S` if and only if it is
the image of a point of `|𝒞urves^{smooth}|`. -/
theorem mem_smoothPointsSet (S : Scheme.{u})
    {x : CohStack.Points (ofObjectProperty (lciPlus S))} :
    x ∈ smoothPointsSet S ↔
      ∃ y : CohStack.Points (ofObjectProperty (smooth S)),
        CohStack.Points.map (inclusionSmoothLciPlus S) y = x :=
  sorry

/-- The induced map on points of `inclusionSmoothLciPlus S` is an open embedding. -/
theorem isOpenEmbedding_pointsMap_inclusionSmoothLciPlus (S : Scheme.{u}) :
    Topology.IsOpenEmbedding (CohStack.Points.map (inclusionSmoothLciPlus S)) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
