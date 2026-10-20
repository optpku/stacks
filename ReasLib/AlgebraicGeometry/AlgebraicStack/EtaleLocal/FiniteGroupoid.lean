module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OfScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object

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
algebraic spaces, from a quotient stack `(SmallQuotient.quotientStack (ofScheme G))`
onto a given point of `X`, where `G` is a groupoid scheme with affine object
and arrow schemes and with finite, flat, locally of finite presentation source
and target. -/
def existsEtaleLocalAffineFiniteGroupoidAt {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) : Prop :=
  ∃ (G : GroupoidScheme S)
      (_ : AlgebraicStack (SmallQuotient.quotientStack (ofScheme G)))
      (f : (SmallQuotient.quotientStack (ofScheme G)) ⟶ X)
      (u : Points (SmallQuotient.quotientStack (ofScheme G))),
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
          (_ : AlgebraicStack (SmallQuotient.quotientStack (ofScheme G)))
          (f : (SmallQuotient.quotientStack (ofScheme G)) ⟶ X)
          (u : Points (SmallQuotient.quotientStack (ofScheme G))),
        Points.map f u = x ∧ relativelyRepresentableByAlgebraicSpaces f ∧
          Groupoids.Hom.Etale f ∧ IsAffine G.U.left ∧ IsAffine G.R.left ∧
            IsFinite G.s.left ∧ IsFinite G.t.left ∧
            AlgebraicGeometry.Flat G.s.left ∧ AlgebraicGeometry.Flat G.t.left ∧
            AlgebraicGeometry.LocallyOfFinitePresentation G.s.left ∧
            AlgebraicGeometry.LocallyOfFinitePresentation G.t.left :=
  Iff.rfl

/-- An étale, space-representable morphism from the quotient of an affine
finite flat locally finitely presented groupoid scheme, sending `u` to `x`,
witnesses `existsEtaleLocalAffineFiniteGroupoidAt X x`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (G : GroupoidScheme S)
    [AlgebraicStack (SmallQuotient.quotientStack (ofScheme G))]
    (f : (SmallQuotient.quotientStack (ofScheme G)) ⟶ X)
    (h_repr : relativelyRepresentableByAlgebraicSpaces f)
    [Groupoids.Hom.Etale f] [IsAffine G.U.left] [IsAffine G.R.left]
    [IsFinite G.s.left] [IsFinite G.t.left]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left]
    (u : Points (SmallQuotient.quotientStack (ofScheme G))) (hu : Points.map f u = x) :
    existsEtaleLocalAffineFiniteGroupoidAt X x :=
  ⟨G, inferInstance, f, u, hu, h_repr, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance⟩

/-- `existsEtaleLocalAffineFiniteGroupoidAt X x` supplies an étale,
space-representable chart through an affine finite flat locally finitely
presented groupoid scheme, hitting `x`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : existsEtaleLocalAffineFiniteGroupoidAt X x) :
    ∃ (G : GroupoidScheme S)
        (_ : AlgebraicStack (SmallQuotient.quotientStack (ofScheme G)))
        (f : (SmallQuotient.quotientStack (ofScheme G)) ⟶ X)
        (u : Points (SmallQuotient.quotientStack (ofScheme G))),
      Points.map f u = x ∧ relativelyRepresentableByAlgebraicSpaces f ∧
        Groupoids.Hom.Etale f ∧ IsAffine G.U.left ∧ IsAffine G.R.left ∧
          IsFinite G.s.left ∧ IsFinite G.t.left ∧
          AlgebraicGeometry.Flat G.s.left ∧ AlgebraicGeometry.Flat G.t.left ∧
          AlgebraicGeometry.LocallyOfFinitePresentation G.s.left ∧
          AlgebraicGeometry.LocallyOfFinitePresentation G.t.left :=
  h

end existsEtaleLocalAffineFiniteGroupoidAt

/-- Every point of a quasi-DM algebraic stack with separated diagonal is hit
by a representable étale morphism from the quotient of a groupoid scheme with
affine objects and arrows and finite, flat, locally finitely presented source
and target. -/
theorem existsEtaleLocalAffineFiniteGroupoidAt_of_isQuasiDM {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] [IsQuasiDM X]
    (h_separatedDiagonal :
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (diagonal.{u + 1, u, u + 1} X))
    (x : Points X) : existsEtaleLocalAffineFiniteGroupoidAt X x :=
  sorry

/-- There exists an étale morphism of algebraic stacks, representable by
algebraic spaces, from a quotient stack `(SmallQuotient.quotientStack (ofScheme G))`
onto a given point of `X`, inducing an isomorphism of automorphism groups at
that point, where `G` is a groupoid scheme with affine object and arrow
schemes and with finite, flat, locally of finite presentation source and
target. -/
def existsEtaleLocalAffineFiniteGroupoidIsoAutAt {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) : Prop :=
  ∃ (G : GroupoidScheme S)
      (_ : AlgebraicStack (SmallQuotient.quotientStack (ofScheme G)))
      (f : (SmallQuotient.quotientStack (ofScheme G)) ⟶ X)
      (u : Points (SmallQuotient.quotientStack (ofScheme G))),
    Points.map f u = x ∧ relativelyRepresentableByAlgebraicSpaces f ∧
      Groupoids.Hom.Etale f ∧ IsAffine G.U.left ∧ IsAffine G.R.left ∧
        IsFinite G.s.left ∧ IsFinite G.t.left ∧
        AlgebraicGeometry.Flat G.s.left ∧ AlgebraicGeometry.Flat G.t.left ∧
        AlgebraicGeometry.LocallyOfFinitePresentation G.s.left ∧
        AlgebraicGeometry.LocallyOfFinitePresentation G.t.left ∧
        automorphismGroup.IsIsoAt f u

namespace existsEtaleLocalAffineFiniteGroupoidIsoAutAt

/-- `existsEtaleLocalAffineFiniteGroupoidIsoAutAt X x` unpacks to an étale,
space-representable chart through an affine finite flat locally finitely
presented groupoid scheme, hitting `x` and inducing an isomorphism of
automorphism groups there. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} :
    existsEtaleLocalAffineFiniteGroupoidIsoAutAt X x ↔
      ∃ (G : GroupoidScheme S)
          (_ : AlgebraicStack (SmallQuotient.quotientStack (ofScheme G)))
          (f : (SmallQuotient.quotientStack (ofScheme G)) ⟶ X)
          (u : Points (SmallQuotient.quotientStack (ofScheme G))),
        Points.map f u = x ∧ relativelyRepresentableByAlgebraicSpaces f ∧
          Groupoids.Hom.Etale f ∧ IsAffine G.U.left ∧ IsAffine G.R.left ∧
            IsFinite G.s.left ∧ IsFinite G.t.left ∧
            AlgebraicGeometry.Flat G.s.left ∧ AlgebraicGeometry.Flat G.t.left ∧
            AlgebraicGeometry.LocallyOfFinitePresentation G.s.left ∧
            AlgebraicGeometry.LocallyOfFinitePresentation G.t.left ∧
            automorphismGroup.IsIsoAt f u :=
  Iff.rfl

/-- An étale, space-representable morphism from the quotient of an affine
finite flat locally finitely presented groupoid scheme, sending `u` to `x`
and inducing an isomorphism of automorphism groups at `u`, witnesses
`existsEtaleLocalAffineFiniteGroupoidIsoAutAt X x`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (G : GroupoidScheme S)
    [AlgebraicStack (SmallQuotient.quotientStack (ofScheme G))]
    (f : (SmallQuotient.quotientStack (ofScheme G)) ⟶ X)
    (h_repr : relativelyRepresentableByAlgebraicSpaces f)
    [Groupoids.Hom.Etale f] [IsAffine G.U.left] [IsAffine G.R.left]
    [IsFinite G.s.left] [IsFinite G.t.left]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left]
    (u : Points (SmallQuotient.quotientStack (ofScheme G))) (hu : Points.map f u = x)
    (h_iso : automorphismGroup.IsIsoAt f u) :
    existsEtaleLocalAffineFiniteGroupoidIsoAutAt X x :=
  ⟨G, inferInstance, f, u, hu, h_repr, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, h_iso⟩

/-- `existsEtaleLocalAffineFiniteGroupoidIsoAutAt X x` supplies an étale,
space-representable chart through an affine finite flat locally finitely
presented groupoid scheme, hitting `x` and inducing an isomorphism of
automorphism groups there. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : existsEtaleLocalAffineFiniteGroupoidIsoAutAt X x) :
    ∃ (G : GroupoidScheme S)
        (_ : AlgebraicStack (SmallQuotient.quotientStack (ofScheme G)))
        (f : (SmallQuotient.quotientStack (ofScheme G)) ⟶ X)
        (u : Points (SmallQuotient.quotientStack (ofScheme G))),
      Points.map f u = x ∧ relativelyRepresentableByAlgebraicSpaces f ∧
        Groupoids.Hom.Etale f ∧ IsAffine G.U.left ∧ IsAffine G.R.left ∧
          IsFinite G.s.left ∧ IsFinite G.t.left ∧
          AlgebraicGeometry.Flat G.s.left ∧ AlgebraicGeometry.Flat G.t.left ∧
          AlgebraicGeometry.LocallyOfFinitePresentation G.s.left ∧
          AlgebraicGeometry.LocallyOfFinitePresentation G.t.left ∧
          automorphismGroup.IsIsoAt f u :=
  h

/-- From `existsEtaleLocalAffineFiniteGroupoidIsoAutAt X x` one obtains a
chart morphism through a groupoid-scheme quotient that hits `x` and induces
an isomorphism of automorphism groups there. -/
theorem isIsoAt {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : existsEtaleLocalAffineFiniteGroupoidIsoAutAt X x) :
    ∃ (G : GroupoidScheme S)
        (_ : AlgebraicStack (SmallQuotient.quotientStack (ofScheme G)))
        (f : (SmallQuotient.quotientStack (ofScheme G)) ⟶ X)
        (u : Points (SmallQuotient.quotientStack (ofScheme G))),
      Points.map f u = x ∧ automorphismGroup.IsIsoAt f u :=
  by
    rcases h with ⟨G, hG, f, u, hu, h_repr, h_etale, hU, hR, hs, ht,
      hs_flat, ht_flat, hs_lfp, ht_lfp, h_iso⟩
    exact ⟨G, hG, f, u, hu, h_iso⟩

end existsEtaleLocalAffineFiniteGroupoidIsoAutAt

/-- A point with finite automorphism group on a quasi-DM algebraic stack
with separated diagonal admits a representable étale chart inducing an
isomorphism on automorphism groups, presented by a groupoid scheme with
affine objects and arrows and finite, flat, locally finitely presented source
and target. -/
theorem existsEtaleLocalAffineFiniteGroupoidIsoAutAt_of_isQuasiDM
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsQuasiDM X]
    (h_separatedDiagonal :
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (diagonal.{u + 1, u, u + 1} X))
    {x : Points X} (h_finite : automorphismGroup.IsFinite x) :
    existsEtaleLocalAffineFiniteGroupoidIsoAutAt X x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
