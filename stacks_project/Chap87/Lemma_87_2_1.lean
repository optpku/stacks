module

public import stacks_project.Chap03.Lemma_3_9_2_ObjectProperty
public import stacks_project.Chap87.Lemma_87_2_1_FunctorOfPoints
public import stacks_project.Chap87.Lemma_87_2_1_Size

/-!
# Lemma 87.2.1

The functor of points of a formal scheme, evaluated on a small category of
schemes `Sch_α` as in Sets, Lemma 3.9.2, is fully faithful on morphisms out of
formal schemes whose size is not too large.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.FormalScheme

/-- Lemma 87.2.1. Choose a category of schemes `Sch_α` as in Sets, Lemma 3.9.2.
Given a formal scheme `X`, its functor of points on `(Sch_α)ᵒᵖ` is
`(functorOfPoints P).obj X`, with value
`toFormalScheme.obj (P.ι.obj S) ⟶ X` at a scheme `S` in `Sch_α`. Then
morphisms `X ⟶ Y` of formal schemes are in bijection with morphisms
`(functorOfPoints P).obj X ⟶ (functorOfPoints P).obj Y` provided the size of
`X` is not too large, meaning `X.size` is at most the size of some scheme
satisfying `P`. -/
@[stacks 0AI1]
theorem functorOfPoints_map_bijective {P : ObjectProperty Scheme.{u}}
    (hP : Scheme.IsSmallBoundClosed P) {X Y : FormalScheme.{u}}
    (hX : ∃ S, P S ∧ X.size ≤ S.size) :
    Function.Bijective
      ((functorOfPoints P).map :
        (X ⟶ Y) → ((functorOfPoints P).obj X ⟶ (functorOfPoints P).obj Y)) :=
  sorry

end AlgebraicGeometry.FormalScheme
