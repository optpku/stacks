/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import stacks_project.Chap78.Lemma_78_15_1_Action
public import stacks_project.Chap78.Lemma_78_17_1_Restriction
public import stacks_project.Chap78.Lemma_78_19_7_Saturation
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Remark_94_16_3_Flat
public import stacks_project.Chap94.Remark_94_16_3_LocallyOfFinitePresentation

/-!
# When a quotient stack of a group action is algebraic

The quotient stack `[X / G]` of an action of a group algebraic space `G` on an
algebraic space `X` over an algebraic space `B` over a scheme `S` is algebraic
if and only if some morphism `φ : X' ⟶ X` over `B` has orbit map a surjection
of fppf sheaves and the restricted action groupoid flat and locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open GroupoidAlgebraicSpace
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Action

/-- The orbit map `(g, x') ↦ a(g, φ(x'))` associated to a morphism `φ : X' ⟶ X`
over `B`. -/
def orbitMap {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : Action G) {X' : Over B} (φ : X' ⟶ X.X) : G.X ⊗ X' ⟶ X.X :=
  (G.X ◁ φ) ≫ actionTarget G X

/-- The orbit map is whiskering `φ` followed by the action map. -/
theorem orbitMap_def {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : Action G) {X' : Over B} (φ : X' ⟶ X.X) :
    orbitMap G X φ = (G.X ◁ φ) ≫ actionTarget G X :=
  sorry

/-- On `T`-points over `B`, the orbit map sends `(g, x')` to `a(g, φ(x'))`. -/
theorem orbitMap_apply {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : Action G) {X' : Over B} (φ : X' ⟶ X.X)
    {T : Over B} (g : T ⟶ G.X) (x' : T ⟶ X') :
    lift g x' ≫ orbitMap G X φ = g • (x' ≫ φ) :=
  sorry

/-- Lemma 97.18.2: let `S` be a scheme and let `B` be an algebraic space over
`S`. Let `G` be a group algebraic space over `B`. Let `X` be an algebraic space
over `B` and let `a : G ×_B X ⟶ X` be an action of `G` on `X` over `B`. The
quotient stack `[X / G]` is an algebraic stack if and only if there exists a
morphism of algebraic spaces `φ : X' ⟶ X` such that `G ×_B X' ⟶ X`,
`(g, x') ↦ a(g, φ(x'))` is a surjection of sheaves, and the two projections
`X'' ⟶ X'` of the algebraic space `X''` given by
`T ↦ {(x'₁, g, x'₂) | φ(x'₁) = a(g, φ(x'₂))}` are flat and locally of finite
presentation. Formalized for `G : GroupAlgebraicSpace B` and `X : Action G`,
with `[X / G]` as `(ofAction G X).quotientStack`, the action as
`actionTarget G X`, the orbit map as `orbitMap G X φ`, sheaf surjection as
`Presheaf.IsLocallySurjective` on `Scheme.fppfTopology.over S`, `X''` as
`((ofAction G X).pullback φ).R`, and the two projections flat and locally of
finite presentation as `Flat ((ofAction G X).pullback φ)` and
`LocallyOfFinitePresentation ((ofAction G X).pullback φ)`. -/
@[stacks 06PK]
theorem isAlgebraicStack_quotientStack_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : Action G) :
    AlgebraicStack (ofAction G X).quotientStack ↔
      ∃ (X' : Over B) (φ : X' ⟶ X.X),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (orbitMap G X φ).left ∧
          GroupoidAlgebraicSpace.Flat ((ofAction G X).pullback φ) ∧
            GroupoidAlgebraicSpace.LocallyOfFinitePresentation ((ofAction G X).pullback φ) :=
  sorry

/-- If a morphism `φ : X' ⟶ X` has orbit map a surjection of fppf sheaves and
the restricted action groupoid is flat and locally of finite presentation, then
`[X / G]` is an algebraic stack. -/
theorem isAlgebraicStack_quotientStack_of_orbitMap {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (X : Action G)
    {X' : Over B} (φ : X' ⟶ X.X)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (orbitMap G X φ).left)
    [GroupoidAlgebraicSpace.Flat ((ofAction G X).pullback φ)]
    [GroupoidAlgebraicSpace.LocallyOfFinitePresentation ((ofAction G X).pullback φ)] :
    AlgebraicStack (ofAction G X).quotientStack :=
  sorry

/-- If `[X / G]` is an algebraic stack, then there exists a morphism
`φ : X' ⟶ X` whose orbit map is a surjection of fppf sheaves and whose
restricted action groupoid is flat and locally of finite presentation. -/
theorem exists_orbitMap_of_isAlgebraicStack_quotientStack {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (X : Action G)
    [AlgebraicStack (ofAction G X).quotientStack] :
    ∃ (X' : Over B) (φ : X' ⟶ X.X),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (orbitMap G X φ).left ∧
        GroupoidAlgebraicSpace.Flat ((ofAction G X).pullback φ) ∧
          GroupoidAlgebraicSpace.LocallyOfFinitePresentation ((ofAction G X).pullback φ) :=
  sorry

/-- Source-facing expansion of `isAlgebraicStack_quotientStack_iff`: the two
projections `X'' ⟶ X'` are flat and locally of finite presentation as morphisms
of algebraic spaces. -/
theorem isAlgebraicStack_quotientStack_iff_spec {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (X : Action G) :
    AlgebraicStack (ofAction G X).quotientStack ↔
      ∃ (X' : Over B) (φ : X' ⟶ X.X),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (orbitMap G X φ).left ∧
          AlgebraicSpace.Flat ((ofAction G X).pullback φ).s.left ∧
            AlgebraicSpace.Flat ((ofAction G X).pullback φ).t.left ∧
              AlgebraicSpace.LocallyOfFinitePresentation
                ((ofAction G X).pullback φ).s.left ∧
                AlgebraicSpace.LocallyOfFinitePresentation
                  ((ofAction G X).pullback φ).t.left :=
  sorry

/-- A `T`-point of the restricted arrow space `X''` from `x₂` to `x₁` corresponds
to a `T`-point `g` of `G` satisfying `φ(x'₁) = a(g, φ(x'₂))`. -/
theorem restriction_pointHom_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : Action G) {X' : Over B} (φ : X' ⟶ X.X)
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B} {x₁ x₂ : Over.mk σ ⟶ X'} :
    Nonempty (((ofAction G X).pullback φ).PointHom σ x₂ x₁) ↔
      ∃ g : Over.mk σ ⟶ G.X, x₁ ≫ φ = g • (x₂ ≫ φ) :=
  sorry

/-- The orbit map is an fppf sheaf surjection if and only if the saturation map
of the restricted action groupoid is, via inversion in `G`. -/
theorem locallySurjective_orbitMap_iff_saturationMap {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (X : Action G)
    {X' : Over B} (φ : X' ⟶ X.X) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        (orbitMap G X φ).left ↔
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        ((ofAction G X).saturationMap φ).left :=
  sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Action
