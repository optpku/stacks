/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Lemma_67_38_8_Unramified

/-!
# Pointwise unramifiedness of morphisms of algebraic spaces

A morphism of algebraic spaces is unramified at a point when it is unramified
after restriction to an open subspace neighbourhood, in the sense of Stacks
Definition 67.38.1 (2). The remaining predicates package the equivalent
characterizations of unramified morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces is unramified at a point `x` of
`X` if it is unramified after restriction to some open subspace neighbourhood
of `x`. -/
def UnramifiedAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Unramified (i ≫ f)

/-- Unramifiedness at a point is the existence of an open subspace neighbourhood
on which the morphism is unramified. -/
theorem unramifiedAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    UnramifiedAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Unramified (i ≫ f) :=
  sorry

namespace Unramified

/-- Every base change of `f` along a morphism from a scheme is unramified. -/
def baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y), Unramified (pullbackAlongScheme.snd f g)

/-- Every base change of `f` along a morphism from an affine scheme is
unramified. -/
def baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    IsAffine Z.left → Unramified (pullbackAlongScheme.snd f g)

/-- There is a surjective étale morphism from a scheme to `Y` along which the
base change of `f` is unramified. -/
def existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b ∧
      Surjective b ∧ Unramified (pullbackAlongScheme.snd f b)

/-- There is a surjective étale morphism `φ` from a scheme to `X` such that
`φ ≫ f` is unramified. -/
def existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
      Surjective φ ∧ Unramified (φ ≫ f)

/-- Every étale scheme square over `f` has unramified top arrow. -/
def forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a →
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Unramified h.left

/-- There is an étale scheme square over `f` with surjective source cover and
unramified top arrow. -/
def existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Surjective a ∧ AlgebraicGeometry.Unramified h.left

/-- There are Zariski coverings of `Y` and of the inverse images in `X` on which
the pieces of `f` are unramified. -/
def existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
    ∃ (Xi : AlgebraicSpace S) (ι : Xi ⟶ X) (_ : IsOpenImmersion ι)
      (𝒰 : ZariskiCover.{u, v} Xi) (h : ∀ j, 𝒰.X j ⟶ 𝒱.X i),
      (∀ j, 𝒰.f j ≫ ι ≫ f = h j ≫ 𝒱.f i) ∧
        (∀ j, Unramified (h j)) ∧
          ∀ x : Points X,
            Points.map f x ∈ Set.range (Points.map (𝒱.f i)) →
              x ∈ Set.range (Points.map ι)

end Unramified

end AlgebraicGeometry.AlgebraicSpace
