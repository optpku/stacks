/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_39_1_Etale
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Local characterizations of étaleness for morphisms of algebraic spaces

These predicates package the equivalent local, atlas, square, and Zariski
tests for étale morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

namespace Etale

/-- Every base change of `f` along a morphism from a scheme is étale. -/
def baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y), Etale (pullbackAlongScheme.snd f g)

/-- `baseChangeOnSchemes f` is the assertion that every scheme base change of
`f` is étale. -/
theorem baseChangeOnSchemes_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    baseChangeOnSchemes f ↔
      ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
        Etale (pullbackAlongScheme.snd f g) :=
  sorry

namespace baseChangeOnSchemes

/-- A morphism satisfying `baseChangeOnSchemes` remains étale after every
scheme base change. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : baseChangeOnSchemes f) {Z : Over S} (g : ofOver Z ⟶ Y) :
    Etale (pullbackAlongScheme.snd f g) :=
  sorry

/-- The universal scheme-base-change condition witnesses
`baseChangeOnSchemes f`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
      Etale (pullbackAlongScheme.snd f g)) :
    baseChangeOnSchemes f :=
  sorry

end baseChangeOnSchemes

/-- Every base change of `f` along a morphism from an affine scheme is étale. -/
def baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    IsAffine Z.left → Etale (pullbackAlongScheme.snd f g)

/-- `baseChangeOnAffineSchemes f` is the assertion that every affine scheme
base change of `f` is étale. -/
theorem baseChangeOnAffineSchemes_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    baseChangeOnAffineSchemes f ↔
      ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
        IsAffine Z.left → Etale (pullbackAlongScheme.snd f g) :=
  sorry

namespace baseChangeOnAffineSchemes

/-- A morphism satisfying `baseChangeOnAffineSchemes` remains étale after every
affine scheme base change. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : baseChangeOnAffineSchemes f) {Z : Over S} (g : ofOver Z ⟶ Y)
    (hZ : IsAffine Z.left) : Etale (pullbackAlongScheme.snd f g) :=
  sorry

/-- The universal affine-scheme-base-change condition witnesses
`baseChangeOnAffineSchemes f`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
      IsAffine Z.left → Etale (pullbackAlongScheme.snd f g)) :
    baseChangeOnAffineSchemes f :=
  sorry

end baseChangeOnAffineSchemes

/-- There is a surjective étale morphism from a scheme to `Y` along which the
base change of `f` is étale. -/
def existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b ∧
      Surjective b ∧ Etale (pullbackAlongScheme.snd f b)

/-- `existsSurjectiveEtaleTarget f` is the existence of a surjective étale
scheme atlas of `Y` along which the base change of `f` is étale. -/
theorem existsSurjectiveEtaleTarget_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    existsSurjectiveEtaleTarget f ↔
      ∃ (V : Over S) (b : ofOver V ⟶ Y),
        (over (@AlgebraicGeometry.Etale)).presheaf b ∧
          Surjective b ∧ Etale (pullbackAlongScheme.snd f b) :=
  sorry

namespace existsSurjectiveEtaleTarget

/-- A surjective étale scheme atlas of `Y` along which the base change of `f`
is étale witnesses `existsSurjectiveEtaleTarget f`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {V : Over S}
    (b : ofOver V ⟶ Y) (h_etale : (over (@AlgebraicGeometry.Etale)).presheaf b)
    [Surjective b] [Etale (pullbackAlongScheme.snd f b)] :
    existsSurjectiveEtaleTarget f :=
  sorry

/-- `existsSurjectiveEtaleTarget f` supplies a surjective étale scheme atlas of
`Y` along which the base change of `f` is étale. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : existsSurjectiveEtaleTarget f) :
    ∃ (V : Over S) (b : ofOver V ⟶ Y),
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        Surjective b ∧ Etale (pullbackAlongScheme.snd f b) :=
  sorry

end existsSurjectiveEtaleTarget

/-- There is a surjective étale morphism `φ` from a scheme to `X` such that
`φ ≫ f` is étale. -/
def existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
      Surjective φ ∧ Etale (φ ≫ f)

/-- `existsSurjectiveEtaleSource f` is the existence of a surjective étale
scheme atlas of `X` whose composite with `f` is étale. -/
theorem existsSurjectiveEtaleSource_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    existsSurjectiveEtaleSource f ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X),
        (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
          Surjective φ ∧ Etale (φ ≫ f) :=
  sorry

namespace existsSurjectiveEtaleSource

/-- A surjective étale scheme atlas of `X` with étale composite with `f`
witnesses `existsSurjectiveEtaleSource f`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {U : Over S}
    (φ : ofOver U ⟶ X) (h_etale : (over (@AlgebraicGeometry.Etale)).presheaf φ)
    [Surjective φ] [Etale (φ ≫ f)] : existsSurjectiveEtaleSource f :=
  sorry

/-- `existsSurjectiveEtaleSource f` supplies a surjective étale scheme atlas of
`X` whose composite with `f` is étale. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : existsSurjectiveEtaleSource f) :
    ∃ (U : Over S) (φ : ofOver U ⟶ X),
      (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
        Surjective φ ∧ Etale (φ ≫ f) :=
  sorry

end existsSurjectiveEtaleSource

/-- Every étale scheme square over `f` has étale top arrow. -/
def forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a →
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Etale h.left

/-- `forallEtaleSquare f` is the assertion that every étale scheme square over
`f` has étale top arrow. -/
theorem forallEtaleSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    forallEtaleSquare f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Etale h.left :=
  sorry

namespace forallEtaleSquare

/-- An étale scheme square over a morphism satisfying `forallEtaleSquare` has
étale top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : forallEtaleSquare f) {U V : Over S}
    (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) : AlgebraicGeometry.Etale h.left :=
  sorry

/-- The universal étale-square condition witnesses `forallEtaleSquare f`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hcond : ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
      (over (@AlgebraicGeometry.Etale)).presheaf a →
        (over (@AlgebraicGeometry.Etale)).presheaf b →
          a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Etale h.left) :
    forallEtaleSquare f :=
  sorry

end forallEtaleSquare

/-- There is an étale scheme square over `f` with surjective source cover and
étale top arrow. -/
def existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Surjective a ∧ AlgebraicGeometry.Etale h.left

/-- `existsEtaleSquare f` is the existence of an étale scheme square over `f`
with surjective source cover and étale top arrow. -/
theorem existsEtaleSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    existsEtaleSquare f ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a ∧
          (over (@AlgebraicGeometry.Etale)).presheaf b ∧
            a ≫ f = ofOverMap h ≫ b ∧
              Surjective a ∧ AlgebraicGeometry.Etale h.left :=
  sorry

namespace existsEtaleSquare

/-- An étale scheme square over `f` with surjective source cover and étale top
arrow witnesses `existsEtaleSquare f`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {U V : Over S}
    {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y} {h : U ⟶ V}
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) [Surjective a]
    [AlgebraicGeometry.Etale h.left] : existsEtaleSquare f :=
  sorry

/-- `existsEtaleSquare f` supplies an étale scheme square over `f` with
surjective source cover and étale top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : existsEtaleSquare f) :
    ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V),
      (over (@AlgebraicGeometry.Etale)).presheaf a ∧
        (over (@AlgebraicGeometry.Etale)).presheaf b ∧
          a ≫ f = ofOverMap h ≫ b ∧
            Surjective a ∧ AlgebraicGeometry.Etale h.left :=
  sorry

end existsEtaleSquare

/-- There are Zariski coverings of `Y` and of the inverse images in `X` on which
the pieces of `f` are étale. -/
def existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
    ∃ (Xi : AlgebraicSpace S) (ι : Xi ⟶ X) (_ : IsOpenImmersion ι)
      (𝒰 : ZariskiCover.{u, v} Xi) (h : ∀ j, 𝒰.X j ⟶ 𝒱.X i),
      (∀ j, 𝒰.f j ≫ ι ≫ f = h j ≫ 𝒱.f i) ∧
        (∀ j, Etale (h j)) ∧
          ∀ x : Points X,
            Points.map f x ∈ Set.range (Points.map (𝒱.f i)) →
              x ∈ Set.range (Points.map ι)

/-- `existsZariskiCover f` is the existence of Zariski coverings of `Y` and of
the inverse images in `X` on which the pieces of `f` are étale. -/
theorem existsZariskiCover_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    existsZariskiCover f ↔
      ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
        ∃ (Xi : AlgebraicSpace S) (ι : Xi ⟶ X) (_ : IsOpenImmersion ι)
          (𝒰 : ZariskiCover.{u, v} Xi) (h : ∀ j, 𝒰.X j ⟶ 𝒱.X i),
          (∀ j, 𝒰.f j ≫ ι ≫ f = h j ≫ 𝒱.f i) ∧
            (∀ j, Etale (h j)) ∧
              ∀ x : Points X,
                Points.map f x ∈ Set.range (Points.map (𝒱.f i)) →
                  x ∈ Set.range (Points.map ι) :=
  sorry

namespace existsZariskiCover

/-- Zariski coverings of `Y` and of the inverse images in `X` with étale pieces
witness `existsZariskiCover f`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (𝒱 : ZariskiCover.{u, v} Y)
    (h : ∀ i : 𝒱.I₀,
      ∃ (Xi : AlgebraicSpace S) (ι : Xi ⟶ X) (_ : IsOpenImmersion ι)
        (𝒰 : ZariskiCover.{u, v} Xi) (h : ∀ j, 𝒰.X j ⟶ 𝒱.X i),
        (∀ j, 𝒰.f j ≫ ι ≫ f = h j ≫ 𝒱.f i) ∧
          (∀ j, Etale (h j)) ∧
            ∀ x : Points X,
              Points.map f x ∈ Set.range (Points.map (𝒱.f i)) →
                x ∈ Set.range (Points.map ι)) :
    existsZariskiCover f :=
  sorry

/-- `existsZariskiCover f` supplies Zariski coverings of `Y` and of the inverse
images in `X` on which the pieces of `f` are étale. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : existsZariskiCover f) :
    ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
      ∃ (Xi : AlgebraicSpace S) (ι : Xi ⟶ X) (_ : IsOpenImmersion ι)
        (𝒰 : ZariskiCover.{u, v} Xi) (h : ∀ j, 𝒰.X j ⟶ 𝒱.X i),
        (∀ j, 𝒰.f j ≫ ι ≫ f = h j ≫ 𝒱.f i) ∧
          (∀ j, Etale (h j)) ∧
            ∀ x : Points X,
              Points.map f x ∈ Set.range (Points.map (𝒱.f i)) →
                x ∈ Set.range (Points.map ι) :=
  sorry

end existsZariskiCover

end Etale

end AlgebraicGeometry.AlgebraicSpace
