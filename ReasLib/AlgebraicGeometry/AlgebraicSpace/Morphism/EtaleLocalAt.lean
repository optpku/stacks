module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.EtaleLocal

/-!
# Étale scheme squares through a point of a morphism of algebraic spaces

Properties of scheme-germ morphisms can be tested on étale scheme squares through a
fixed point. For étale-local properties, universal and existential testing agree.
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
  rfl

/-- The morphism of scheme germs `(U.left, u) ⟶ (V.left, h.left u)` induced by a morphism
`h : U ⟶ V` of schemes over `S`. -/
def ofOverGermHom {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) (u : U.left) :
    Scheme.Germ.of U.left u ⟶ Scheme.Germ.of V.left (h.left u) :=
  Scheme.Germ.Hom.ofGlobal h.left (ofOverGermHom_mapPoint h u)

/-- `ofOverGermHom h u` is the germ morphism associated to the global pointed map `h.left`. -/
theorem ofOverGermHom_eq {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) (u : U.left) :
    ofOverGermHom h u =
      (Scheme.Germ.Hom.ofGlobal h.left (ofOverGermHom_mapPoint h u) :
        Scheme.Germ.of U.left u ⟶ Scheme.Germ.of V.left (h.left u)) :=
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

open Scheme.Germ.MorphismProperty

/-- An étale-local property of morphisms of scheme germs holds on every étale scheme square
through a fixed point of an algebraic-space morphism if and only if it holds on some such
square. -/
theorem forallEtaleSquareAt_iff_existsEtaleSquareAt {S : Scheme.{u}}
    {Q : MorphismProperty Scheme.Germ.{u}}
    (hQ : IsEtaleLocal Q)
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    forallEtaleSquareAt Q f x ↔ existsEtaleSquareAt Q f x :=
  sorry

/-- For a morphism of schemes over a base, an étale-local germ property holds on some
étale scheme square through a point if and only if it holds on the induced germ morphism. -/
theorem existsEtaleSquareAt_ofOverMap_iff {S : Scheme.{u}}
    {Q : MorphismProperty Scheme.Germ.{u}}
    (hQ : IsEtaleLocal Q)
    {U V : Over S} (h : U ⟶ V) (u : U.left) :
    existsEtaleSquareAt Q (ofOverMap h) (ofOver.pointsEquiv U u) ↔
      Q (ofOverGermHom h u) :=
  sorry

/-- For a morphism of schemes over a base, an étale-local germ property holds on every
étale scheme square through a point if and only if it holds on the induced germ morphism. -/
theorem forallEtaleSquareAt_ofOverMap_iff {S : Scheme.{u}}
    {Q : MorphismProperty Scheme.Germ.{u}}
    (hQ : IsEtaleLocal Q)
    {U V : Over S} (h : U ⟶ V) (u : U.left) :
    forallEtaleSquareAt Q (ofOverMap h) (ofOver.pointsEquiv U u) ↔
      Q (ofOverGermHom h u) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
