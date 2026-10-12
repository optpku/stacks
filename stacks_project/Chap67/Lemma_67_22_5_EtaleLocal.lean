/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.EtaleLocal
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology

/-!
# Étale scheme squares through a point of a morphism of algebraic spaces

A property `Q` of morphisms of scheme germs may be tested on étale scheme squares
over a morphism of algebraic spaces through a fixed source point: the “for any
square” and “for some square” conditions are the basic predicates.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- The global pointed map `h.left` sends the distinguished point of `(U.left, u)` to the
distinguished point of `(V.left, h.left u)`. -/
theorem ofOverGermHom_mapPoint {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) (u : U.left) :
    h.left (Scheme.Germ.of U.left u).point =
      (Scheme.Germ.of V.left (h.left u)).point :=
  sorry

/-- The morphism of scheme germs `(U.left, u) ⟶ (V.left, h.left u)` induced by a morphism
`h : U ⟶ V` of schemes over `S`. -/
def ofOverGermHom {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) (u : U.left) :
    Scheme.Germ.of U.left u ⟶ Scheme.Germ.of V.left (h.left u) :=
  @Scheme.Germ.Hom.ofGlobal (Scheme.Germ.of U.left u) (Scheme.Germ.of V.left (h.left u))
    h.left (ofOverGermHom_mapPoint h u)

/-- `ofOverGermHom h u` is the germ morphism associated to the global pointed map `h.left`. -/
theorem ofOverGermHom_eq {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) (u : U.left) :
    ofOverGermHom h u =
      @Scheme.Germ.Hom.ofGlobal (Scheme.Germ.of U.left u) (Scheme.Germ.of V.left (h.left u))
        h.left (ofOverGermHom_mapPoint h u) :=
  rfl

/-- There exists an étale scheme square over `f` through `x` whose induced germ morphism
satisfies `Q`. -/
def existsEtaleSquareAt {S : Scheme.{u}} (Q : MorphismProperty Scheme.Germ.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) : Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left),
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Points.mapOfOver a u = x ∧ Q (ofOverGermHom h u)

/-- `existsEtaleSquareAt Q f x` is the existence of an étale scheme square through `x` on
which `Q` holds. -/
theorem existsEtaleSquareAt_def {S : Scheme.{u}} (Q : MorphismProperty Scheme.Germ.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    existsEtaleSquareAt Q f x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b ∧
            a ≫ f = ofOverMap h ≫ b ∧
              Points.mapOfOver a u = x ∧ Q (ofOverGermHom h u) :=
  Iff.rfl

namespace existsEtaleSquareAt

/-- An étale scheme square over `f` through `x` on which `Q` holds witnesses
`existsEtaleSquareAt Q f x`. -/
theorem of {S : Scheme.{u}} {Q : MorphismProperty Scheme.Germ.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X} {U V : Over S}
    (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x)
    (hQ : Q (ofOverGermHom h u)) : existsEtaleSquareAt Q f x :=
  ⟨U, V, a, b, h, u, ha, hb, w, hx, hQ⟩

/-- A morphism satisfying `existsEtaleSquareAt Q f x` admits an étale scheme square through
`x` on which `Q` holds. -/
theorem spec {S : Scheme.{u}} {Q : MorphismProperty Scheme.Germ.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X}
    (h : existsEtaleSquareAt Q f x) :
    ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b ∧
          a ≫ f = ofOverMap h ≫ b ∧
            Points.mapOfOver a u = x ∧ Q (ofOverGermHom h u) :=
  h

end existsEtaleSquareAt

/-- Every étale scheme square over `f` through `x` has induced germ morphism satisfying `Q`. -/
def forallEtaleSquareAt {S : Scheme.{u}} (Q : MorphismProperty Scheme.Germ.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) : Prop :=
  ∀ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left),
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b →
        a ≫ f = ofOverMap h ≫ b →
          Points.mapOfOver a u = x → Q (ofOverGermHom h u)

/-- `forallEtaleSquareAt Q f x` is the statement that every étale scheme square through `x`
has property `Q` on the induced germ morphism. -/
theorem forallEtaleSquareAt_def {S : Scheme.{u}} (Q : MorphismProperty Scheme.Germ.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    forallEtaleSquareAt Q f x ↔
      ∀ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = ofOverMap h ≫ b →
              Points.mapOfOver a u = x → Q (ofOverGermHom h u) :=
  Iff.rfl

namespace forallEtaleSquareAt

/-- The universal étale-scheme-square-through-`x` condition witnesses
`forallEtaleSquareAt Q f x`. -/
theorem of {S : Scheme.{u}} {Q : MorphismProperty Scheme.Germ.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X}
    (h : ∀ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b →
          a ≫ f = ofOverMap h ≫ b →
            Points.mapOfOver a u = x → Q (ofOverGermHom h u)) :
    forallEtaleSquareAt Q f x :=
  h

/-- If `forallEtaleSquareAt Q f x`, then every étale scheme square over `f` through `x` has
property `Q` on the induced germ morphism. -/
theorem apply {S : Scheme.{u}} {Q : MorphismProperty Scheme.Germ.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X}
    (hf : forallEtaleSquareAt Q f x) {U V : Over S}
    (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x) :
    Q (ofOverGermHom h u) :=
  hf U V a b h u ha hb w hx

end forallEtaleSquareAt

/-- The second point square of an étale scheme square through `x`: the image of `h.left u`
under `b` is the image of `x` under `f`. -/
theorem etaleSquare_points_comm {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (f : X ⟶ Y)
    (u : U.left) {x : Points X} (w : a ≫ f = ofOverMap h ≫ b)
    (hx : Points.mapOfOver a u = x) :
    Points.mapOfOver b (h.left u) = Points.map f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

