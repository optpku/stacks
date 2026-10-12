/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology

/-!
# Residue-field transcendence degree of a morphism of algebraic spaces

The transcendence degree of a point `x` of `X` over its image under `f : X ⟶ Y`
is the étale-local invariant `trdeg` of `x/f(x)` from Stacks Definition 67.33.1,
computed on any étale scheme square through `x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The transcendence degree of a point `x` of `X` over its image under a morphism
`f : X ⟶ Y` of algebraic spaces, as the supremum of scheme-level residue-field
transcendence degrees along étale scheme squares through `x`. -/
noncomputable def residueFieldTrdegAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) : ℕ :=
  ⨆ (U : Over S) (V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (u : U.left) (_ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (_hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (_w : a ≫ f = ofOverMap h ≫ b) (_hx : Points.mapOfOver a u = x),
    Scheme.Hom.residueFieldTrdegAt h.left u

/-- The residue-field transcendence degree of `f` at `x` equals the scheme-level
residue-field transcendence degree of the top arrow of any étale scheme square
through `x`. -/
theorem residueFieldTrdegAt_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (u : U.left) {x : Points X}
    (hx : Points.mapOfOver a u = x) :
    residueFieldTrdegAt f x = Scheme.Hom.residueFieldTrdegAt h.left u :=
  sorry

/-- On a morphism of schemes over `S`, viewed as a morphism of algebraic spaces,
the residue-field transcendence degree recovers the scheme-level invariant. -/
theorem residueFieldTrdegAt_ofOverMap {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (u : U.left) :
    residueFieldTrdegAt (ofOverMap h) (ofOver.pointsEquiv U u) =
      Scheme.Hom.residueFieldTrdegAt h.left u :=
  sorry

namespace residueFieldTrdegAt

/-- Every point of the source of a morphism of algebraic spaces lies on an étale
scheme square over that morphism. -/
theorem exists_etaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
      (u : U.left),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b ∧
          a ≫ f = ofOverMap h ≫ b ∧ Points.mapOfOver a u = x :=
  sorry

end residueFieldTrdegAt

end AlgebraicGeometry.AlgebraicSpace
