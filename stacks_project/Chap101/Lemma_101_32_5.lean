module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap94.Definition_94_12_2_Etale
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Example_100_12_5_Quotient
public import stacks_project.Chap100.Lemma_100_14_1_QuasiCompact
public import stacks_project.Chap100.Example_100_11_9_ResidualGerbe
public import stacks_project.Chap100.Lemma_100_11_14
public import stacks_project.Chap101.Definition_101_4_2_Separation

/-!
# Étale-local affine finite groupoid charts inducing residual-gerbe isomorphisms

A quasi-DM algebraic stack with separated diagonal, at a point represented by a
quasi-compact morphism `Spec(k) ⟶ X`, admits an étale morphism representable by
algebraic spaces from a quotient stack `[U / R]` of a groupoid scheme with
affine objects and arrows and with finite, flat, locally of finite presentation
source and target, hitting the point and inducing an isomorphism of residual
gerbes there.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks sends `u` to `x` and induces an isomorphism of
residual gerbes at those points: some residual-gerbe inclusions `ιu` at `u` and
`ιx` at `x` admit a 2-commutative comparison 1-morphism whose underlying based
functor is an equivalence. -/
def inducesIsoOnResidualGerbes {S : Scheme.{u}} {U X : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] (f : U ⟶ X) (u : Points U)
    (x : Points X) : Prop :=
  Points.map f u = x ∧
    ∃ (Zu Zx : GroupoidsOver S) (_ : AlgebraicStack Zu) (_ : AlgebraicStack Zx)
      (ιu : Zu ⟶ U) (ιx : Zx ⟶ X) (h : Zu ⟶ Zx),
      IsResidualGerbe ιu u ∧ IsResidualGerbe ιx x ∧
        (toBasedFunctor h).IsEquivalence ∧ Nonempty (h ≫ ιx ≅ ιu ≫ f)

namespace inducesIsoOnResidualGerbes

/-- `inducesIsoOnResidualGerbes f u x` unpacks to `Points.map f u = x` together
with residual-gerbe inclusions at `u` and `x` and a 2-commutative comparison
that is a based-functor equivalence. -/
theorem iff {S : Scheme.{u}} {U X : GroupoidsOver S} [AlgebraicStack U]
    [AlgebraicStack X] (f : U ⟶ X) (u : Points U) (x : Points X) :
    inducesIsoOnResidualGerbes f u x ↔
      Points.map f u = x ∧
        ∃ (Zu Zx : GroupoidsOver S) (_ : AlgebraicStack Zu)
          (_ : AlgebraicStack Zx) (ιu : Zu ⟶ U) (ιx : Zx ⟶ X) (h : Zu ⟶ Zx),
          IsResidualGerbe ιu u ∧ IsResidualGerbe ιx x ∧
            (toBasedFunctor h).IsEquivalence ∧ Nonempty (h ≫ ιx ≅ ιu ≫ f) :=
  sorry

/-- A point-mapping morphism together with residual-gerbe inclusions and a
2-commutative based-functor equivalence between them witnesses
`inducesIsoOnResidualGerbes f u x`. -/
theorem of {S : Scheme.{u}} {U X Zu Zx : GroupoidsOver S} [AlgebraicStack U]
    [AlgebraicStack X] [AlgebraicStack Zu] [AlgebraicStack Zx] (f : U ⟶ X)
    {u : Points U} {x : Points X} (hu : Points.map f u = x) (ιu : Zu ⟶ U)
    (ιx : Zx ⟶ X) [IsResidualGerbe ιu u] [IsResidualGerbe ιx x] (h : Zu ⟶ Zx)
    (h_equiv : (toBasedFunctor h).IsEquivalence)
    (h_comm : Nonempty (h ≫ ιx ≅ ιu ≫ f)) :
    inducesIsoOnResidualGerbes f u x :=
  sorry

/-- `inducesIsoOnResidualGerbes f u x` supplies `Points.map f u = x` together
with residual-gerbe inclusions at `u` and `x` and a 2-commutative comparison
that is a based-functor equivalence. -/
theorem spec {S : Scheme.{u}} {U X : GroupoidsOver S} [AlgebraicStack U]
    [AlgebraicStack X] {f : U ⟶ X} {u : Points U} {x : Points X}
    (h : inducesIsoOnResidualGerbes f u x) :
    Points.map f u = x ∧
      ∃ (Zu Zx : GroupoidsOver S) (_ : AlgebraicStack Zu)
        (_ : AlgebraicStack Zx) (ιu : Zu ⟶ U) (ιx : Zx ⟶ X) (h : Zu ⟶ Zx),
        IsResidualGerbe ιu u ∧ IsResidualGerbe ιx x ∧
          (toBasedFunctor h).IsEquivalence ∧ Nonempty (h ≫ ιx ≅ ιu ≫ f) :=
  sorry

end inducesIsoOnResidualGerbes

/-- There exists an étale morphism of algebraic stacks, representable by
algebraic spaces, from a quotient stack `(ofGroupoidScheme G).quotientStack`
onto a given point of `X`, inducing an isomorphism of residual gerbes at that
point, where `G` is a groupoid scheme with affine object and arrow schemes and
with finite, flat, locally of finite presentation source and target. -/
def existsEtaleLocalAffineFiniteGroupoidIsoResidualGerbeAt {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) : Prop :=
  ∃ (G : GroupoidScheme S)
      (_ : AlgebraicStack (ofGroupoidScheme G).quotientStack)
      (f : (ofGroupoidScheme G).quotientStack ⟶ X)
      (u : Points (ofGroupoidScheme G).quotientStack),
    relativelyRepresentableByAlgebraicSpaces f ∧ Groupoids.Hom.Etale f ∧
      IsAffine G.U.left ∧ IsAffine G.R.left ∧ IsFinite G.s.left ∧
        IsFinite G.t.left ∧ AlgebraicGeometry.Flat G.s.left ∧
        AlgebraicGeometry.Flat G.t.left ∧
        AlgebraicGeometry.LocallyOfFinitePresentation G.s.left ∧
        AlgebraicGeometry.LocallyOfFinitePresentation G.t.left ∧
        inducesIsoOnResidualGerbes f u x

/-- `existsEtaleLocalAffineFiniteGroupoidIsoResidualGerbeAt X x` unpacks to an
étale, space-representable chart through an affine finite flat locally finitely
presented groupoid scheme, hitting `x` and inducing an isomorphism of residual
gerbes there. -/
theorem existsEtaleLocalAffineFiniteGroupoidIsoResidualGerbeAt_iff
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X} :
    existsEtaleLocalAffineFiniteGroupoidIsoResidualGerbeAt X x ↔
      ∃ (G : GroupoidScheme S)
          (_ : AlgebraicStack (ofGroupoidScheme G).quotientStack)
          (f : (ofGroupoidScheme G).quotientStack ⟶ X)
          (u : Points (ofGroupoidScheme G).quotientStack),
        relativelyRepresentableByAlgebraicSpaces f ∧ Groupoids.Hom.Etale f ∧
          IsAffine G.U.left ∧ IsAffine G.R.left ∧ IsFinite G.s.left ∧
            IsFinite G.t.left ∧ AlgebraicGeometry.Flat G.s.left ∧
            AlgebraicGeometry.Flat G.t.left ∧
            AlgebraicGeometry.LocallyOfFinitePresentation G.s.left ∧
            AlgebraicGeometry.LocallyOfFinitePresentation G.t.left ∧
            inducesIsoOnResidualGerbes f u x :=
  sorry

/-- An étale, space-representable morphism from the quotient of an affine
finite flat locally finitely presented groupoid scheme, sending `u` to `x`
and inducing an isomorphism of residual gerbes there, witnesses
`existsEtaleLocalAffineFiniteGroupoidIsoResidualGerbeAt X x`. -/
theorem existsEtaleLocalAffineFiniteGroupoidIsoResidualGerbeAt_of
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (G : GroupoidScheme S)
    [AlgebraicStack (ofGroupoidScheme G).quotientStack]
    (f : (ofGroupoidScheme G).quotientStack ⟶ X)
    (h_repr : relativelyRepresentableByAlgebraicSpaces f)
    [Groupoids.Hom.Etale f] [IsAffine G.U.left] [IsAffine G.R.left]
    [IsFinite G.s.left] [IsFinite G.t.left]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left]
    (u : Points (ofGroupoidScheme G).quotientStack)
    (h_iso : inducesIsoOnResidualGerbes f u x) :
    existsEtaleLocalAffineFiniteGroupoidIsoResidualGerbeAt X x :=
  sorry

/-- `existsEtaleLocalAffineFiniteGroupoidIsoResidualGerbeAt X x` supplies an
étale, space-representable chart through an affine finite flat locally finitely
presented groupoid scheme, hitting `x` and inducing an isomorphism of residual
gerbes there. -/
theorem existsEtaleLocalAffineFiniteGroupoidIsoResidualGerbeAt_spec
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X}
    (h : existsEtaleLocalAffineFiniteGroupoidIsoResidualGerbeAt X x) :
    ∃ (G : GroupoidScheme S)
        (_ : AlgebraicStack (ofGroupoidScheme G).quotientStack)
        (f : (ofGroupoidScheme G).quotientStack ⟶ X)
        (u : Points (ofGroupoidScheme G).quotientStack),
      relativelyRepresentableByAlgebraicSpaces f ∧ Groupoids.Hom.Etale f ∧
        IsAffine G.U.left ∧ IsAffine G.R.left ∧ IsFinite G.s.left ∧
          IsFinite G.t.left ∧ AlgebraicGeometry.Flat G.s.left ∧
          AlgebraicGeometry.Flat G.t.left ∧
          AlgebraicGeometry.LocallyOfFinitePresentation G.s.left ∧
          AlgebraicGeometry.LocallyOfFinitePresentation G.t.left ∧
          inducesIsoOnResidualGerbes f u x :=
  sorry

/-- Lemma 101.32.5: Let `X` be an algebraic stack. Assume `X` is quasi-DM with
separated diagonal (equivalently the inertia morphism `I_X ⟶ X` is locally
quasi-finite and separated, by Lemma 101.6.1). Let `x : Points X`. Assume `x`
can be represented by a quasi-compact morphism `Spec(k) ⟶ X`
(`existsQuasiCompactFieldValuedPoint`). Then there exists a morphism of
algebraic stacks `f : 𝒰 ⟶ X` such that there is a point `u : Points 𝒰`
mapping to `x` and `f` induces an isomorphism of residual gerbes at `u` and
`x`, `f` is `relativelyRepresentableByAlgebraicSpaces` and
`Groupoids.Hom.Etale`, and `𝒰 = (ofGroupoidScheme G).quotientStack` for a
groupoid scheme `(U, R, s, t, c)` with `IsAffine G.U.left`,
`IsAffine G.R.left`, and with `IsFinite`, `AlgebraicGeometry.Flat`, and
`AlgebraicGeometry.LocallyOfFinitePresentation` of both `G.s.left` and
`G.t.left`. -/
@[stacks 0DU5]
theorem existsEtaleLocalAffineFiniteGroupoidIsoResidualGerbeAt_of_isQuasiDM
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsQuasiDM X]
    (h_separatedDiagonal :
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (diagonal.{u + 1, u, u + 1} X))
    {x : Points X} (hx : existsQuasiCompactFieldValuedPoint X x) :
    existsEtaleLocalAffineFiniteGroupoidIsoResidualGerbeAt X x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
