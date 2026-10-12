/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Syntomic morphisms of algebraic spaces

A morphism of algebraic spaces is syntomic when every étale scheme square over
it has syntomic top arrow, in the sense of Stacks Definition 67.36.1 (1).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is syntomic if every
commutative square with étale vertical arrows from schemes has syntomic top
arrow. -/
class Syntomic {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Every étale scheme square over `f` has syntomic top arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.Syntomic h.left

/-- A morphism of algebraic spaces is syntomic if and only if every commutative
square with étale vertical arrows from schemes has syntomic top arrow. -/
theorem syntomic_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Syntomic f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Syntomic h.left :=
  sorry

namespace Syntomic

/-- An étale scheme square over a syntomic morphism of algebraic spaces has
syntomic top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Syntomic f]
    {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) : AlgebraicGeometry.Syntomic h.left :=
  sorry

/-- The identity morphism of an algebraic space is syntomic. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Syntomic (𝟙 X) :=
  sorry

end Syntomic

/-- A morphism `f : X ⟶ Y` of algebraic spaces is syntomic at a point `x` of `X`
if it is syntomic after restriction to some open subspace neighbourhood of
`x`. -/
def SyntomicAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Syntomic (i ≫ f)

/-- Syntomicity at a point is the existence of an open subspace neighbourhood on
which the morphism is syntomic. -/
theorem syntomicAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    SyntomicAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Syntomic (i ≫ f) :=
  sorry

namespace Syntomic

/-- Every base change of `f` along a morphism from a scheme is syntomic. -/
def baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y), Syntomic (pullbackAlongScheme.snd f g)

/-- Every base change of `f` along a morphism from an affine scheme is
syntomic. -/
def baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    IsAffine Z.left → Syntomic (pullbackAlongScheme.snd f g)

/-- There is a surjective étale morphism from a scheme to `Y` along which the
base change of `f` is syntomic. -/
def existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b ∧
      Surjective b ∧ Syntomic (pullbackAlongScheme.snd f b)

/-- There is a surjective étale morphism `φ` from a scheme to `X` such that
`φ ≫ f` is syntomic. -/
def existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
      Surjective φ ∧ Syntomic (φ ≫ f)

/-- Every étale scheme square over `f` has syntomic top arrow. -/
def forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a →
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Syntomic h.left

/-- There is an étale scheme square over `f` with surjective source cover and
syntomic top arrow. -/
def existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Surjective a ∧ AlgebraicGeometry.Syntomic h.left

/-- There are Zariski coverings of `Y` and of the inverse images in `X` on which
the pieces of `f` are syntomic. -/
def existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
    ∃ (Xi : AlgebraicSpace S) (ι : Xi ⟶ X) (_ : IsOpenImmersion ι)
      (𝒰 : ZariskiCover.{u, v} Xi) (h : ∀ j, 𝒰.X j ⟶ 𝒱.X i),
      (∀ j, 𝒰.f j ≫ ι ≫ f = h j ≫ 𝒱.f i) ∧
        (∀ j, Syntomic (h j)) ∧
          ∀ x : Points X,
            Points.map f x ∈ Set.range (Points.map (𝒱.f i)) →
              x ∈ Set.range (Points.map ι)

end Syntomic

end AlgebraicGeometry.AlgebraicSpace
