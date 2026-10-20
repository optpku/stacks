module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Topology.Defs.Induced
public import stacks_project.Chap109.Lemma_109_16_6
public import stacks_project.Chap109.Lemma_109_17_1_Points
public import stacks_project.Chap109.Lemma_109_22_7_Substack

/-!
# Inclusion of smooth proper genus-`g` curves into stable curves

For `2 ≤ g`, the object property of `ℳ_g` is contained in that of `ℳ̄_g`.
The induced 1-morphism of full subcategories of `𝒞urves` is an open
immersion, and the image of `CohStack.Points.map` is the source-facing
subset `|ℳ_g| ⊂ |ℳ̄_g|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The full subcategory of `𝒞urves` cut out by `smoothH0OfGenus g` is an
algebraic stack in the Hom-universe of `CohStack.toGroupoids`. -/
instance instAlgebraicStack_ofObjectProperty_smoothH0OfGenus
    (g : ℕ) (S : Scheme.{u}) :
    CohStack.AlgebraicStack (ofObjectProperty (smoothH0OfGenus g S)) :=
  sorry

/-- For `2 ≤ g`, membership in `smoothH0OfGenus g` implies membership in
`stableOfGenus g`. -/
theorem smoothH0OfGenus_le_stableOfGenus (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    smoothH0OfGenus g S ≤ stableOfGenus g S :=
  sorry

/-- For `2 ≤ g`, the intersection of `𝒞urves^{smooth}` with `ℳ̄_g` is `ℳ_g`. -/
theorem smooth_inf_stableOfGenus_eq (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    (fun P ↦ AlgebraicSpace.Smooth (hom P)) ⊓ stableOfGenus g S =
      smoothH0OfGenus g S :=
  sorry

/-- For `2 ≤ g`, a family is smooth and stable of genus `g` if and only if it
lies in `ℳ_g`. -/
theorem smooth_and_stableOfGenus_iff_smoothH0OfGenus
    (g : ℕ) (hg : 2 ≤ g) {S : Scheme.{u}} (P : Obj S) :
    AlgebraicSpace.Smooth (hom P) ∧ stableOfGenus g S P ↔
      smoothH0OfGenus g S P :=
  sorry

/-- The inclusion of `ℳ_g` into `ℳ̄_g`, as a 1-morphism of categories
fibred in groupoids over `Over S`. -/
def inclusionSmoothStableOfGenus (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    ofObjectProperty (smoothH0OfGenus g S) ⟶
      ofObjectProperty (stableOfGenus g S) :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    { toFunctor := ιOfLE (smoothH0OfGenus_le_stableOfGenus g hg S)
      w := sorry }

/-- The underlying functor of `inclusionSmoothStableOfGenus g hg S` is the
identity-on-carriers map of `smoothH0OfGenus_le_stableOfGenus`. -/
theorem inclusionSmoothStableOfGenus_toFunctor
    (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    FiberedCategoryOver.Groupoids.toFunctor
        (inclusionSmoothStableOfGenus g hg S) =
      ιOfLE (smoothH0OfGenus_le_stableOfGenus g hg S) :=
  sorry

/-- The triangle of inclusions of `ℳ_g` and `ℳ̄_g` into `𝒞urves`. -/
theorem inclusionSmoothStableOfGenus_comp_inclusionOf
    (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    inclusionSmoothStableOfGenus g hg S ≫ inclusionOf (stableOfGenus g S) =
      inclusionOf (smoothH0OfGenus g S) :=
  sorry

/-- The inclusion of `ℳ_g` into `ℳ̄_g` is an open immersion. -/
instance instOpenImmersion_inclusionSmoothStableOfGenus
    (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    CohStack.Hom.OpenImmersion (inclusionSmoothStableOfGenus g hg S) :=
  sorry

/-- The set of points of `ℳ̄_g` in the image of `|ℳ_g| → |ℳ̄_g|`. -/
def smoothH0OfGenusPointsSet (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    Set (CohStack.Points (ofObjectProperty (stableOfGenus g S))) :=
  Set.range (CohStack.Points.map (inclusionSmoothStableOfGenus g hg S))

/-- `smoothH0OfGenusPointsSet g hg S` is the range of `CohStack.Points.map`
of `inclusionSmoothStableOfGenus g hg S`. -/
theorem smoothH0OfGenusPointsSet_eq (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    smoothH0OfGenusPointsSet g hg S =
      Set.range (CohStack.Points.map (inclusionSmoothStableOfGenus g hg S)) :=
  sorry

/-- A point of `|ℳ̄_g|` lies in `smoothH0OfGenusPointsSet g hg S` if and
only if it is the image of a point of `|ℳ_g|`. -/
theorem mem_smoothH0OfGenusPointsSet (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u})
    {x : CohStack.Points (ofObjectProperty (stableOfGenus g S))} :
    x ∈ smoothH0OfGenusPointsSet g hg S ↔
      ∃ y : CohStack.Points (ofObjectProperty (smoothH0OfGenus g S)),
        CohStack.Points.map (inclusionSmoothStableOfGenus g hg S) y = x :=
  sorry

/-- The induced map on points of `inclusionSmoothStableOfGenus g hg S` is an
open embedding. -/
theorem isOpenEmbedding_pointsMap_inclusionSmoothStableOfGenus
    (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    Topology.IsOpenEmbedding
      (CohStack.Points.map (inclusionSmoothStableOfGenus g hg S)) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
