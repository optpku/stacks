module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal
public import Mathlib.Data.List.TFAE
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Étale-local tests for morphisms of algebraic spaces

Étaleness can be tested on a surjective étale scheme atlas of the source or target,
or on a commutative square with an étale horizontal morphism of schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

namespace Etale

/-- Every base change of a morphism along a morphism from a scheme is étale. -/
def baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y), Etale (pullbackAlongScheme.snd f g)

/-- The scheme base-change test is equivalent to étaleness of every projection
obtained by base change along a morphism from a scheme. -/
theorem baseChangeOnSchemes_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    baseChangeOnSchemes f ↔
      ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
        Etale (pullbackAlongScheme.snd f g) := Iff.rfl

namespace baseChangeOnSchemes

/-- The scheme base-change test gives an étale projection after each scheme
base change. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : baseChangeOnSchemes f) {Z : Over S} (g : ofOver Z ⟶ Y) :
    Etale (pullbackAlongScheme.snd f g) := hf g

/-- Étaleness of every scheme base-change projection implies the scheme
base-change test. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
      Etale (pullbackAlongScheme.snd f g)) :
    baseChangeOnSchemes f := h

end baseChangeOnSchemes

/-- Every base change of a morphism along a morphism from an affine scheme is étale. -/
def baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    IsAffine Z.left → Etale (pullbackAlongScheme.snd f g)

/-- The affine scheme base-change test is equivalent to étaleness of every
projection obtained by base change along a morphism from an affine scheme. -/
theorem baseChangeOnAffineSchemes_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    baseChangeOnAffineSchemes f ↔
      ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
        IsAffine Z.left → Etale (pullbackAlongScheme.snd f g) := Iff.rfl

namespace baseChangeOnAffineSchemes

/-- The affine scheme base-change test gives an étale projection after each
affine scheme base change. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : baseChangeOnAffineSchemes f) {Z : Over S} (g : ofOver Z ⟶ Y)
    (hZ : IsAffine Z.left) : Etale (pullbackAlongScheme.snd f g) := hf g hZ

/-- Étaleness of every affine scheme base-change projection implies the affine
scheme base-change test. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
      IsAffine Z.left → Etale (pullbackAlongScheme.snd f g)) :
    baseChangeOnAffineSchemes f := h

end baseChangeOnAffineSchemes

/-- There is a Zariski covering of the target such that each inverse image
has a Zariski covering whose composites to the target chart are étale. -/
def existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
    ∃ 𝒰 : ZariskiCover.{u, v} (Limits.pullback f (𝒱.f i)), ∀ j : 𝒰.I₀,
      Etale (𝒰.f j ≫ Limits.pullback.snd f (𝒱.f i))

/-- The Zariski test is equivalent to the existence of target and inverse-image
coverings with étale composites to each target chart. -/
theorem existsZariskiCover_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    existsZariskiCover.{u, v} f ↔
      ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
        ∃ 𝒰 : ZariskiCover.{u, v} (Limits.pullback f (𝒱.f i)), ∀ j : 𝒰.I₀,
          Etale (𝒰.f j ≫ Limits.pullback.snd f (𝒱.f i)) := Iff.rfl

namespace existsZariskiCover

/-- Target and inverse-image Zariski coverings with étale composites to the
target charts satisfy the Zariski test. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (𝒱 : ZariskiCover.{u, v} Y)
    (h : ∀ i : 𝒱.I₀,
      ∃ 𝒰 : ZariskiCover.{u, v} (Limits.pullback f (𝒱.f i)), ∀ j : 𝒰.I₀,
        Etale (𝒰.f j ≫ Limits.pullback.snd f (𝒱.f i))) :
    existsZariskiCover.{u, v} f := ⟨𝒱, h⟩

/-- The Zariski test supplies target and inverse-image coverings with étale
composites to each target chart. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : existsZariskiCover.{u, v} f) :
    ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
      ∃ 𝒰 : ZariskiCover.{u, v} (Limits.pullback f (𝒱.f i)), ∀ j : 𝒰.I₀,
        Etale (𝒰.f j ≫ Limits.pullback.snd f (𝒱.f i)) := h

end existsZariskiCover

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- There is a surjective étale morphism from a scheme to `X` whose composite
with `f` is étale as a morphism of algebraic spaces. -/
def existsOnSource : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧ Etale (φ ≫ f)

/-- The source-atlas test is the existence of a surjective étale scheme atlas
of `X` whose composite with `f` is étale. -/
theorem existsOnSource_iff : existsOnSource f ↔
    ∃ (U : Over S) (φ : ofOver U ⟶ X),
      (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧
          Etale (φ ≫ f) := Iff.rfl

namespace existsOnSource

/-- A surjective étale scheme atlas of `X` with étale composite with `f`
satisfies the source-atlas test. -/
theorem of {U : Over S} (φ : ofOver U ⟶ X)
    (h_etale : (over (@AlgebraicGeometry.Etale)).presheaf φ)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ)
    [Etale (φ ≫ f)] : existsOnSource f :=
  ⟨U, φ, h_etale, h_surj, inferInstance⟩

/-- The source-atlas test supplies a surjective étale scheme atlas of `X`
whose composite with `f` is étale. -/
theorem spec (h : existsOnSource f) :
    ∃ (U : Over S) (φ : ofOver U ⟶ X),
      (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧
          Etale (φ ≫ f) := h

end existsOnSource

/-- There is a surjective étale morphism from a scheme to `Y` and a pullback
of `f` along it whose projection to that scheme is étale. -/
def existsOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf ψ ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) ψ ∧
        ∃ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f ∧ Etale pV

/-- The target-atlas test is the existence of a surjective étale scheme atlas
of `Y` and a pullback square with étale projection to that atlas. -/
theorem existsOnTarget_iff : existsOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      (over (@AlgebraicGeometry.Etale)).presheaf ψ ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) ψ ∧
          ∃ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
            IsPullback pV pX ψ f ∧ Etale pV := Iff.rfl

namespace existsOnTarget

/-- A surjective étale scheme atlas of `Y` and a pullback square with étale
projection to the atlas satisfy the target-atlas test. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y)
    (h_etale : (over (@AlgebraicGeometry.Etale)).presheaf ψ)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) ψ)
    {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X}
    (sq : IsPullback pV pX ψ f) (hpV : Etale pV) : existsOnTarget f :=
  ⟨V, ψ, h_etale, h_surj, P, pV, pX, sq, hpV⟩

/-- The target-atlas test supplies a surjective étale scheme atlas of `Y`
and a pullback square with étale projection to the atlas. -/
theorem spec (h : existsOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      (over (@AlgebraicGeometry.Etale)).presheaf ψ ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) ψ ∧
          ∃ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
            IsPullback pV pX ψ f ∧ Etale pV := h

end existsOnTarget

/-- There is a commutative square of schemes over `f` with étale vertical
arrows, surjective left vertical arrow, and étale horizontal arrow. -/
def existsSquare : Prop :=
  ∃ (U V : Over S) (φ : ofOver U ⟶ X) (ψ : ofOver V ⟶ Y) (h : U ⟶ V),
    CommSq (yoneda.map h) φ ψ f ∧
      (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧
          (over (@AlgebraicGeometry.Etale)).presheaf ψ ∧
            AlgebraicGeometry.Etale h.left

/-- The square test is the existence of a commutative square of schemes over
`f` with étale vertical arrows, surjective left edge, and étale horizontal arrow. -/
theorem existsSquare_iff : existsSquare f ↔
    ∃ (U V : Over S) (φ : ofOver U ⟶ X) (ψ : ofOver V ⟶ Y) (h : U ⟶ V),
      CommSq (yoneda.map h) φ ψ f ∧
        (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧
            (over (@AlgebraicGeometry.Etale)).presheaf ψ ∧
              AlgebraicGeometry.Etale h.left := Iff.rfl

namespace existsSquare

/-- A commutative square of schemes with étale vertical arrows, surjective
left vertical arrow, and étale horizontal arrow satisfies the square test. -/
theorem of {U V : Over S} {φ : ofOver U ⟶ X} {ψ : ofOver V ⟶ Y} {h : U ⟶ V}
    (sq : CommSq (yoneda.map h) φ ψ f)
    (hφ_etale : (over (@AlgebraicGeometry.Etale)).presheaf φ)
    (hφ_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ)
    (hψ_etale : (over (@AlgebraicGeometry.Etale)).presheaf ψ)
    [AlgebraicGeometry.Etale h.left] : existsSquare f :=
  ⟨U, V, φ, ψ, h, sq, hφ_etale, hφ_surj, hψ_etale, inferInstance⟩

/-- The square test supplies a commutative square of schemes over `f` with
étale vertical arrows, surjective left edge, and étale horizontal arrow. -/
theorem spec (h : existsSquare f) :
    ∃ (U V : Over S) (φ : ofOver U ⟶ X) (ψ : ofOver V ⟶ Y) (h : U ⟶ V),
      CommSq (yoneda.map h) φ ψ f ∧
        (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧
            (over (@AlgebraicGeometry.Etale)).presheaf ψ ∧
              AlgebraicGeometry.Etale h.left := h

end existsSquare

/-- Étaleness of a morphism of algebraic spaces is equivalent to the source-atlas,
target-atlas, and commutative-square tests. -/
theorem tfae :
    List.TFAE [Etale f, existsOnSource f, existsOnTarget f, existsSquare f] := sorry

/-- A morphism of algebraic spaces is étale iff some surjective étale scheme
atlas of the source has étale composite with it. -/
theorem iff_existsOnSource : Etale f ↔ existsOnSource f :=
  (tfae f).out 0 1

/-- A morphism of algebraic spaces is étale iff some surjective étale scheme
atlas of the target admits an étale base-change projection. -/
theorem iff_existsOnTarget : Etale f ↔ existsOnTarget f :=
  (tfae f).out 0 2

/-- A morphism of algebraic spaces is étale iff there is a commutative square
of schemes over it with étale vertical arrows, surjective left edge, and
étale horizontal arrow. -/
theorem iff_existsSquare : Etale f ↔ existsSquare f :=
  (tfae f).out 0 3

end Etale

/-- Étaleness of a morphism of algebraic spaces is equivalent to pointwise
étaleness, the scheme and affine scheme base-change tests, the target and source
atlas tests, the universal and existential étale scheme-square tests, and the
Zariski covering test on target charts and their inverse images. -/
theorem etale_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ Etale f
      , ∀ x : Points X, EtaleAt f x
      , Etale.baseChangeOnSchemes f
      , Etale.baseChangeOnAffineSchemes f
      , Etale.existsOnTarget f
      , Etale.existsOnSource f
      , etaleLocal (fun _ _ h ↦ AlgebraicGeometry.Etale h) f
      , Etale.existsSquare f
      , Etale.existsZariskiCover.{u, v} f ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
