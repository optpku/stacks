/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Flat morphisms of algebraic spaces

A morphism of algebraic spaces is flat when every étale scheme square over it
has flat top arrow, in the sense of Stacks Definition 67.30.1 (1). Flatness at
a point is the presentation-wise germ condition of Definition 67.30.1 (2).
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is flat if every
commutative square with étale vertical arrows from schemes has flat top
arrow. -/
class Flat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Every étale scheme square over `f` has flat top arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.Flat h.left

/-- A morphism of algebraic spaces is flat if and only if every commutative
square with étale vertical arrows from schemes has flat top arrow. -/
theorem flat_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Flat f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Flat h.left :=
  sorry

namespace Flat

/-- An étale scheme square over a flat morphism of algebraic spaces has flat
top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f]
    {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) : AlgebraicGeometry.Flat h.left :=
  sorry

/-- The identity morphism of an algebraic space is flat. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Flat (𝟙 X) :=
  sorry

end Flat

/-- A morphism `f : X ⟶ Y` of algebraic spaces is flat at a point `x` of `X` if
some étale scheme square over `f` has top arrow flat at a point of `U` mapping
to `x`. -/
def FlatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (u : U.left),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Points.map a (ofOver.pointsEquiv U u) = x ∧
            Scheme.Hom.flatAt h.left u

/-- Flatness at a point is the existence of an étale scheme presentation whose
top arrow is flat at a germ mapping to that point. -/
theorem flatAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    FlatAt f x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
        (u : U.left),
        (over (@AlgebraicGeometry.Etale)).presheaf a ∧
          (over (@AlgebraicGeometry.Etale)).presheaf b ∧
            a ≫ f = ofOverMap h ≫ b ∧
              Points.map a (ofOver.pointsEquiv U u) = x ∧
                Scheme.Hom.flatAt h.left u :=
  sorry

/-- A morphism of schemes over `S`, viewed as a morphism of algebraic spaces, is
flat if and only if the underlying morphism of schemes is flat. -/
theorem flat_ofOverMap_iff {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) :
    Flat (ofOverMap h) ↔ AlgebraicGeometry.Flat h.left :=
  sorry

namespace Flat

/-- Every base change of `f` along a morphism from a scheme is flat. -/
def baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y), Flat (pullbackAlongScheme.snd f g)

/-- Every base change of `f` along a morphism from an affine scheme is flat. -/
def baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    IsAffine Z.left → Flat (pullbackAlongScheme.snd f g)

/-- There is a surjective étale morphism from a scheme to `Y` along which the
base change of `f` is flat. -/
def existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b ∧
      Surjective b ∧ Flat (pullbackAlongScheme.snd f b)

/-- There is a surjective étale morphism `φ` from a scheme to `X` such that
`φ ≫ f` is flat. -/
def existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    (over (@AlgebraicGeometry.Etale)).presheaf φ ∧ Surjective φ ∧ Flat (φ ≫ f)

/-- Every étale scheme square over `f` has flat top arrow. -/
def forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a →
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Flat h.left

/-- There is an étale scheme square over `f` with surjective source cover and
flat top arrow. -/
def existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Surjective a ∧ AlgebraicGeometry.Flat h.left

/-- There are Zariski coverings of `Y` and of the inverse images in `X` on which
the pieces of `f` are flat. -/
def existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
    ∃ (Xi : AlgebraicSpace S) (ι : Xi ⟶ X) (_ : IsOpenImmersion ι)
      (𝒰 : ZariskiCover.{u, v} Xi) (h : ∀ j, 𝒰.X j ⟶ 𝒱.X i),
      (∀ j, 𝒰.f j ≫ ι ≫ f = h j ≫ 𝒱.f i) ∧
        (∀ j, Flat (h j)) ∧
          ∀ x : Points X,
            Points.map f x ∈ Set.range (Points.map (𝒱.f i)) →
              x ∈ Set.range (Points.map ι)

end Flat

end AlgebraicGeometry.AlgebraicSpace
