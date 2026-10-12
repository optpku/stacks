/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Definition_85_27_1_Cartesian
public import stacks_project.Chap85.Definition_85_27_3_Nerve
public import stacks_project.Chap85.Lemma_85_31_2_RelatedPoints

/-!
# Related-point classes

If `π : Y ⟶ f.simplicialScheme` is cartesian, then the sets `relatedPoints y`
are equivalence classes of points of `Y _⦋0⦌`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Simplicial

universe u

namespace AlgebraicGeometry

/-- Lemma 85.31.1 (1): if `π : Y ⟶ f.simplicialScheme` is a cartesian morphism of
simplicial schemes, then for every point `y` of `Y _⦋0⦌` one has
`y ∈ relatedPoints y`. -/
@[stacks 024G]
theorem self_mem_relatedPoints {X S : Scheme.{u}} (f : X ⟶ S)
    (Y : SimplicialObject Scheme.{u}) (π : Y ⟶ f.simplicialScheme)
    [SimplicialObject.IsCartesian π] (y : Y _⦋0⦌) :
    y ∈ relatedPoints y :=
  sorry

/-- Lemma 85.31.1 (2): if `π : Y ⟶ f.simplicialScheme` is a cartesian morphism of
simplicial schemes, then for points `y`, `y'` of `Y _⦋0⦌` a nonempty intersection
`relatedPoints y ∩ relatedPoints y'` implies `relatedPoints y = relatedPoints y'`. -/
@[stacks 024G]
theorem relatedPoints_eq_of_inter_nonempty {X S : Scheme.{u}} (f : X ⟶ S)
    (Y : SimplicialObject Scheme.{u}) (π : Y ⟶ f.simplicialScheme)
    [SimplicialObject.IsCartesian π] (y y' : Y _⦋0⦌) :
    (relatedPoints y ∩ relatedPoints y').Nonempty → relatedPoints y = relatedPoints y' :=
  sorry

/-- Membership in `relatedPoints y` is an equivalence relation on points of `Y _⦋0⦌`. -/
theorem relatedPoints_equivalence {X S : Scheme.{u}} (f : X ⟶ S)
    (Y : SimplicialObject Scheme.{u}) (π : Y ⟶ f.simplicialScheme)
    [SimplicialObject.IsCartesian π] :
    Equivalence (fun y y' : Y _⦋0⦌ ↦ y' ∈ relatedPoints y) :=
  sorry

end AlgebraicGeometry
