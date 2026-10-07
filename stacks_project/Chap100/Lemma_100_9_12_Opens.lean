module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Topology.Sets.Opens
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap100.Lemma_100_4_7_Topology
public import stacks_project.Chap100.Lemma_100_9_10_Substack
public import stacks_project.Chap100.Lemma_100_9_11_Substack

/-!
# Opens of points of an algebraic stack

An open substack `U ⊂ X` determines the subset `|U| ⊆ |X|` as the image of
`Points.map U.ι`. This image is open in the canonical topology of Lemma 100.4.7,
and every open of `|X|` arises uniquely up to equality of `objectProperty` from
an open substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.OpenSubstack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The underlying set of points of an open substack, as the image of `|U| → |X|`. -/
def pointsSet (U : OpenSubstack X) : Set (Points X) :=
  Set.range (Points.map U.ι)

/-- `pointsSet U` is the range of `Points.map U.ι`. -/
theorem pointsSet_eq (U : OpenSubstack X) :
    U.pointsSet = Set.range (Points.map U.ι) :=
  sorry

/-- A point of `|X|` lies in `pointsSet U` if and only if it is the image of a
point of `|U.Y|`. -/
theorem mem_pointsSet (U : OpenSubstack X) {x : Points X} :
    x ∈ U.pointsSet ↔ ∃ y : Points U.Y, Points.map U.ι y = x :=
  sorry

/-- The image `|U| ⊆ |X|` is open in the canonical topology on `|X|`. -/
theorem isOpen_pointsSet (U : OpenSubstack X) : IsOpen U.pointsSet :=
  sorry

/-- The image `|U| ⊆ |X|` as an open of the topological space `|X|`. -/
def pointsOpens (U : OpenSubstack X) : Opens (Points X) :=
  Opens.mk U.pointsSet (isOpen_pointsSet U)

/-- The carrier of `pointsOpens U` is `U.pointsSet`. -/
theorem pointsOpens_carrier (U : OpenSubstack X) :
    U.pointsOpens.carrier = U.pointsSet :=
  sorry

/-- The full subcategory of objects of `X` whose Yoneda 1-morphism has image of
points contained in `W`. -/
def ofOpensObjects (W : Opens (Points X)) : ObjectProperty X.total :=
  fun y ↦ Set.range (Points.map
      (YonedaSlice.representative (⟨y, rfl⟩ : X.p.Fiber (X.p.obj y)))) ⊆ W

/-- A total object of `X` lies in `ofOpensObjects W` if and only if the Yoneda
representative has image of points contained in `W`. -/
theorem mem_ofOpensObjects (W : Opens (Points X)) (y : X.total) :
    ofOpensObjects W y ↔
      Set.range (Points.map
          (YonedaSlice.representative (⟨y, rfl⟩ : X.p.Fiber (X.p.obj y)))) ⊆ W :=
  sorry

/-- The restricted projection of `ofOpensObjects W` remains fibred in groupoids. -/
instance instIsFiberedInGroupoids_ofOpensObjects (W : Opens (Points X)) :
    Functor.IsFibered.InGroupoids ((ofOpensObjects W).ι ⋙ X.p) :=
  sorry

/-- The full subcategory of objects with Yoneda image of points in `W` is an
algebraic stack. -/
instance instAlgebraicStack_ofOpens (W : Opens (Points X)) :
    AlgebraicStack (ofFunctor ((ofOpensObjects W).ι ⋙ X.p)) :=
  sorry

/-- The inclusion of `ofOpensObjects W` is an open immersion. -/
instance instOpenImmersion_inclusionOf_ofOpensObjects (W : Opens (Points X)) :
    OpenImmersion (inclusionOf X (ofOpensObjects W)) :=
  sorry

/-- The open substack of `X` occupying the open `W ⊆ |X|`. -/
def ofOpens (W : Opens (Points X)) : OpenSubstack X :=
  ofι (inclusionOf X (ofOpensObjects W))

/-- The objects of `ofOpens W` are `ofOpensObjects W`. -/
theorem ofOpens_objectProperty (W : Opens (Points X)) :
    (ofOpens W).objectProperty = ofOpensObjects W :=
  sorry

/-- The underlying point-set of `ofOpens W` is `W`. -/
theorem ofOpens_pointsSet (W : Opens (Points X)) :
    (ofOpens W).pointsSet = W :=
  sorry

/-- The open substack `ofOpens W` occupies the open `W`, and is unique up to
equality of `objectProperty`. -/
theorem ofOpens_spec (W : Opens (Points X)) :
    (ofOpens W).pointsSet = W ∧
      ∀ V : OpenSubstack X, V.pointsSet = W →
        V.objectProperty = (ofOpens W).objectProperty :=
  sorry

/-- Every open of `|X|` is the point-set of an open substack of `X`, unique up to
equality of `objectProperty`. -/
theorem exists_of_isOpen (W : Set (Points X)) (hW : IsOpen W) :
    ∃ U : OpenSubstack X, U.pointsSet = W ∧
      ∀ V : OpenSubstack X, V.pointsSet = W → V.objectProperty = U.objectProperty :=
  sorry

/-- Inclusion of underlying point-sets of open substacks is equivalent to
inequality of `objectProperty`. -/
theorem pointsSet_subset_iff (U V : OpenSubstack X) :
    U.pointsSet ⊆ V.pointsSet ↔ U.objectProperty ≤ V.objectProperty :=
  sorry

/-- A morphism of open substacks over `X` exists up to 2-isomorphism if and only
if the corresponding point-sets are nested. -/
theorem factorsThrough_iff_pointsSet_subset (U V : OpenSubstack X) :
    FactorsThrough U.ι V.ι ↔ U.pointsSet ⊆ V.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicStack.OpenSubstack
