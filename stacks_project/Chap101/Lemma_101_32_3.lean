module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap94.Definition_94_12_2_Etale
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Example_100_12_5_Quotient
public import stacks_project.Chap101.Definition_101_4_2_Separation

/-!
# Étale-local affine finite groupoid presentations of quasi-DM stacks

A quasi-DM algebraic stack with separated diagonal admits, at every point, an
étale morphism representable by algebraic spaces from a quotient stack
`[U / R]` of a groupoid scheme with affine objects and arrows and with finite,
flat, locally of finite presentation source and target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists an étale morphism of algebraic stacks, representable by
algebraic spaces, from a quotient stack `(ofGroupoidScheme G).quotientStack`
onto a given point of `X`, where `G` is a groupoid scheme with affine object
and arrow schemes and with finite, flat, locally of finite presentation source
and target. -/
def existsEtaleLocalAffineFiniteGroupoidAt {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) : Prop :=
  ∃ (G : GroupoidScheme S)
      (_ : AlgebraicStack (ofGroupoidScheme G).quotientStack)
      (f : (ofGroupoidScheme G).quotientStack ⟶ X)
      (u : Points (ofGroupoidScheme G).quotientStack),
    Points.map f u = x ∧ relativelyRepresentableByAlgebraicSpaces f ∧
      Groupoids.Hom.Etale f ∧ IsAffine G.U.left ∧ IsAffine G.R.left ∧
        IsFinite G.s.left ∧ IsFinite G.t.left ∧
        AlgebraicGeometry.Flat G.s.left ∧ AlgebraicGeometry.Flat G.t.left ∧
        AlgebraicGeometry.LocallyOfFinitePresentation G.s.left ∧
        AlgebraicGeometry.LocallyOfFinitePresentation G.t.left

namespace existsEtaleLocalAffineFiniteGroupoidAt

/-- `existsEtaleLocalAffineFiniteGroupoidAt X x` unpacks to an étale,
space-representable chart through an affine finite flat locally finitely
presented groupoid scheme, hitting `x`. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} :
    existsEtaleLocalAffineFiniteGroupoidAt X x ↔
      ∃ (G : GroupoidScheme S)
          (_ : AlgebraicStack (ofGroupoidScheme G).quotientStack)
          (f : (ofGroupoidScheme G).quotientStack ⟶ X)
          (u : Points (ofGroupoidScheme G).quotientStack),
        Points.map f u = x ∧ relativelyRepresentableByAlgebraicSpaces f ∧
          Groupoids.Hom.Etale f ∧ IsAffine G.U.left ∧ IsAffine G.R.left ∧
            IsFinite G.s.left ∧ IsFinite G.t.left ∧
            AlgebraicGeometry.Flat G.s.left ∧ AlgebraicGeometry.Flat G.t.left ∧
            AlgebraicGeometry.LocallyOfFinitePresentation G.s.left ∧
            AlgebraicGeometry.LocallyOfFinitePresentation G.t.left :=
  sorry

/-- An étale, space-representable morphism from the quotient of an affine
finite flat locally finitely presented groupoid scheme, sending `u` to `x`,
witnesses `existsEtaleLocalAffineFiniteGroupoidAt X x`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (G : GroupoidScheme S)
    [AlgebraicStack (ofGroupoidScheme G).quotientStack]
    (f : (ofGroupoidScheme G).quotientStack ⟶ X)
    (h_repr : relativelyRepresentableByAlgebraicSpaces f)
    [Groupoids.Hom.Etale f] [IsAffine G.U.left] [IsAffine G.R.left]
    [IsFinite G.s.left] [IsFinite G.t.left]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left]
    (u : Points (ofGroupoidScheme G).quotientStack) (hu : Points.map f u = x) :
    existsEtaleLocalAffineFiniteGroupoidAt X x :=
  sorry

/-- `existsEtaleLocalAffineFiniteGroupoidAt X x` supplies an étale,
space-representable chart through an affine finite flat locally finitely
presented groupoid scheme, hitting `x`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : existsEtaleLocalAffineFiniteGroupoidAt X x) :
    ∃ (G : GroupoidScheme S)
        (_ : AlgebraicStack (ofGroupoidScheme G).quotientStack)
        (f : (ofGroupoidScheme G).quotientStack ⟶ X)
        (u : Points (ofGroupoidScheme G).quotientStack),
      Points.map f u = x ∧ relativelyRepresentableByAlgebraicSpaces f ∧
        Groupoids.Hom.Etale f ∧ IsAffine G.U.left ∧ IsAffine G.R.left ∧
          IsFinite G.s.left ∧ IsFinite G.t.left ∧
          AlgebraicGeometry.Flat G.s.left ∧ AlgebraicGeometry.Flat G.t.left ∧
          AlgebraicGeometry.LocallyOfFinitePresentation G.s.left ∧
          AlgebraicGeometry.LocallyOfFinitePresentation G.t.left :=
  sorry

end existsEtaleLocalAffineFiniteGroupoidAt

/-- Lemma 101.32.3: Let `X` be an algebraic stack. Assume `X` is quasi-DM with
separated diagonal (equivalently the inertia morphism `I_X ⟶ X` is locally
quasi-finite and separated, by Lemma 101.6.1). Let `x : Points X`. Then there
exists a morphism of algebraic stacks `f : 𝒰 ⟶ X` such that there is a point
`u : Points 𝒰` with `Points.map f u = x`, `f` is
`relativelyRepresentableByAlgebraicSpaces` and `Groupoids.Hom.Etale`, and
`𝒰 = (ofGroupoidScheme G).quotientStack` for a groupoid scheme
`(U, R, s, t, c)` with `IsAffine G.U.left`, `IsAffine G.R.left`, and with
`IsFinite`, `AlgebraicGeometry.Flat`, and
`AlgebraicGeometry.LocallyOfFinitePresentation` of both `G.s.left` and
`G.t.left`. -/
@[stacks 0DU3]
theorem existsEtaleLocalAffineFiniteGroupoidAt_of_isQuasiDM {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] [IsQuasiDM X]
    (h_separatedDiagonal :
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (diagonal.{u + 1, u, u + 1} X))
    (x : Points X) : existsEtaleLocalAffineFiniteGroupoidAt X x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
