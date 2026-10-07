module

public import stacks_project.Chap67.Lemma_67_22_5_EtaleLocal

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Scheme.Germ.MorphismProperty

/-- Definition 67.22.6: let `Q` be a property of morphisms of germs of schemes
which is étale local on the source-and-target. Let `S` be a scheme. Given a
morphism `f : X ⟶ Y` of algebraic spaces over `S` and a point `x` of `|X|`, we
say that `f` has property `Q` at `x` if the equivalent conditions of
Lemma 67.22.5 hold. -/
@[stacks 04RE]
def etaleLocalAt {S : Scheme.{u}} (Q : MorphismProperty Scheme.Germ.{u})
    (hQ : IsEtaleLocal Q) {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) : Prop :=
  existsEtaleSquareAt Q f x

/-- `etaleLocalAt Q hQ f x` is the existence of an étale scheme square through `x`
on which `Q` holds. -/
theorem etaleLocalAt_def {S : Scheme.{u}} (Q : MorphismProperty Scheme.Germ.{u})
    (hQ : IsEtaleLocal Q) {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    etaleLocalAt Q hQ f x ↔ existsEtaleSquareAt Q f x :=
  Iff.rfl

namespace etaleLocalAt

/-- An étale scheme square over `f` through `x` on which `Q` holds witnesses
`etaleLocalAt Q hQ f x`. -/
theorem of {S : Scheme.{u}} {Q : MorphismProperty Scheme.Germ.{u}}
    (hQ : IsEtaleLocal Q) {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X}
    {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x)
    (hQu : Q (ofOverGermHom h u)) : etaleLocalAt Q hQ f x :=
  existsEtaleSquareAt.of a b h u ha hb w hx hQu

/-- A morphism satisfying `etaleLocalAt Q hQ f x` admits an étale scheme square
through `x` on which `Q` holds. -/
theorem spec {S : Scheme.{u}} {Q : MorphismProperty Scheme.Germ.{u}}
    (hQ : IsEtaleLocal Q) {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X}
    (h : etaleLocalAt Q hQ f x) :
    ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b ∧
          a ≫ f = ofOverMap h ≫ b ∧
            Points.mapOfOver a u = x ∧ Q (ofOverGermHom h u) :=
  h

end etaleLocalAt

/-- If `Q` is étale local on the source-and-target, then `f` has property `Q` at `x`
if and only if every étale scheme square through `x` has property `Q` on the
induced germ morphism. -/
theorem etaleLocalAt_iff_forallEtaleSquareAt {S : Scheme.{u}}
    (Q : MorphismProperty Scheme.Germ.{u}) (hQ : IsEtaleLocal Q)
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    etaleLocalAt Q hQ f x ↔ forallEtaleSquareAt Q f x :=
  sorry

/-- If `X` and `Y` are representable, then `ofOverMap h` has property `Q` at the
image of `u` if and only if `Q` holds on the germ morphism
`(U.left, u) ⟶ (V.left, h.left u)`. -/
theorem etaleLocalAt_ofOverMap_iff {S : Scheme.{u}}
    (Q : MorphismProperty Scheme.Germ.{u}) (hQ : IsEtaleLocal Q)
    {U V : Over S} (h : U ⟶ V) (u : U.left) :
    etaleLocalAt Q hQ (ofOverMap h) (ofOver.pointsEquiv U u) ↔ Q (ofOverGermHom h u) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
