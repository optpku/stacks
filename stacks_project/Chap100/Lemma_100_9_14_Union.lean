/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap94.Lemma_94_14_3_Pullback
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Lemma_100_9_10_Substack

/-!
# Union of open substacks

A family of open substacks of an algebraic stack has a canonical union,
constructed as the strictly full subcategory of objects whose Yoneda
base-changes to the members are jointly surjective on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack.OpenSubstack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The projection `(U ×_X T) ⟶ T` of the 2-fibre product of an open
substack `U ⊂ X` along the Yoneda representative of an object `x` of `X`
over `T = X.p.obj x`. -/
noncomputable abbrev yonedaFibreFst (U : OpenSubstack X) (x : X.total) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (YonedaSlice.representative (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x))) U.ι ⟶
      GroupoidsOver.slice (X.p.obj x) :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u}
    (YonedaSlice.representative (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x))) U.ι

/-- The covering predicate for a family of open substacks: an object `x` of
`X` over `T` lies in the union when the family
`yonedaFibreFst (U i) x : (U i) ×_X T ⟶ T` is jointly surjective on points. -/
def objectProperty_iUnion {I : Type v} (U : I → OpenSubstack X) :
    ObjectProperty X.total :=
  fun x ↦ ∀ t : Points (GroupoidsOver.slice (X.p.obj x)),
    ∃ i, t ∈ Set.range (Points.map (yonedaFibreFst (U i) x))

/-- An object of `X` satisfies `objectProperty_iUnion U` if and only if the
Yoneda base-changes of the members `U i` jointly cover the test slice. -/
theorem objectProperty_iUnion_iff {I : Type v} (U : I → OpenSubstack X)
    (x : X.total) :
    objectProperty_iUnion U x ↔
      ∀ t : Points (GroupoidsOver.slice (X.p.obj x)),
        ∃ i, t ∈ Set.range (Points.map (yonedaFibreFst (U i) x)) := sorry

/-- The covering subcategory of a family of open substacks remains fibred in
groupoids over `Over S`. -/
instance instIsFiberedInGroupoids_objectProperty_iUnion {I : Type v}
    (U : I → OpenSubstack X) :
    Functor.IsFibered.InGroupoids ((objectProperty_iUnion U).ι ⋙ X.p) := sorry

/-- The covering subcategory of a family of open substacks is an algebraic
stack. -/
instance instAlgebraicStack_iUnion {I : Type v} (U : I → OpenSubstack X) :
    AlgebraicStack (ofFunctor ((objectProperty_iUnion U).ι ⋙ X.p)) := sorry

/-- The inclusion of the covering subcategory of a family of open substacks is
an open immersion. -/
instance instOpenImmersion_inclusionOf_iUnion {I : Type v}
    (U : I → OpenSubstack X) :
    OpenImmersion (inclusionOf X (objectProperty_iUnion U)) := sorry

/-- The union open substack `⋃ i, U i` of a family of open substacks of `X`. -/
def iUnion {I : Type v} (U : I → OpenSubstack X) : OpenSubstack X :=
  ofι (inclusionOf X (objectProperty_iUnion U))

/-- Objects of a member `U i` satisfy the covering predicate of the union. -/
theorem mem_objectProperty_iUnion {I : Type v} (U : I → OpenSubstack X)
    (i : I) (x : (U i).Y.total) :
    objectProperty_iUnion U ((toFunctor (U i).ι).obj x) := sorry

/-- The canonical open-substack inclusion `U i ⟶ iUnion U`. -/
def iUnionι {I : Type v} (U : I → OpenSubstack X) (i : I) :
    (U i).Y ⟶ (iUnion U).Y :=
  ofBasedFunctor
    { toFunctor := (objectProperty_iUnion U).lift (toFunctor (U i).ι)
        (mem_objectProperty_iUnion U i)
      w := sorry }

/-- The canonical factorization `U i ⟶ iUnion U` is an open immersion. -/
instance instOpenImmersion_iUnionι {I : Type v} (U : I → OpenSubstack X)
    (i : I) : OpenImmersion (iUnionι U i) := sorry

/-- The canonical factorization `U i ⟶ iUnion U` presents a strictly full
subcategory. -/
instance instIsStrictlyFull_iUnionι {I : Type v} (U : I → OpenSubstack X)
    (i : I) : IsStrictlyFull (iUnionι U i) := sorry

/-- Factorization of the inclusion of a member through the union:
`iUnionι U i ≫ (iUnion U).ι = (U i).ι`. -/
theorem iUnionι_comp {I : Type v} (U : I → OpenSubstack X) (i : I) :
    iUnionι U i ≫ (iUnion U).ι = (U i).ι := sorry

/-- The points of the union are the union of the points of the members. -/
theorem points_iUnion {I : Type v} (U : I → OpenSubstack X) :
    Set.range (Points.map (iUnion U).ι) =
      ⋃ i, Set.range (Points.map (U i).ι) := sorry

end AlgebraicGeometry.AlgebraicStack.OpenSubstack
