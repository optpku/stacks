/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import Mathlib.Data.List.TFAE

/-!
# Locality of quasi-affine morphisms of algebraic spaces

Quasi-affineness is equivalent to representable quasi-affineness and can be tested
on a surjective étale scheme atlas or a Zariski covering of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace QuasiAffine

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is quasi-affine. -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → QuasiAffine pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which the projection `V ×_Y X ⟶ V` is quasi-affine. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → QuasiAffine pV := Iff.rfl

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with quasi-affine pullback
projections of `f` witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → QuasiAffine pV) : existsEtaleOnTarget f :=
  ⟨V, ψ, inferInstance, inferInstance, h⟩

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullback projections of `f` are quasi-affine. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → QuasiAffine pV := h

end existsEtaleOnTarget

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is quasi-affine. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → QuasiAffine pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` map quasi-affinely to the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → QuasiAffine pYi := Iff.rfl

namespace existsZariskiCover

/-- A Zariski covering of `Y` with quasi-affine inverse-image projections of
`f` witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → QuasiAffine pYi) :
    existsZariskiCover f := ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map quasi-affinely to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → QuasiAffine pYi := h

end existsZariskiCover

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `f` is representable and quasi-affine;
`QuasiAffine f`; some scheme `V` with a surjective étale morphism `V ⟶ Y` has
`V ×_Y X ⟶ V` quasi-affine; and some Zariski covering `Y = ⋃ Yᵢ` has each
inverse-image morphism `f⁻¹(Yᵢ) ⟶ Yᵢ` quasi-affine. -/
theorem tfae :
    List.TFAE [(over (@QuasiAffineHom : MorphismProperty Scheme.{u})).presheaf f,
      QuasiAffine f, existsEtaleOnTarget f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is quasi-affine iff it is representable and
quasi-affine on scheme-valued base changes. -/
theorem iff_over_presheaf :
    QuasiAffine f ↔
      (over (@QuasiAffineHom : MorphismProperty Scheme.{u})).presheaf f :=
  (tfae f).out 1 0

/-- A morphism of algebraic spaces is quasi-affine iff some surjective étale
scheme atlas of the target has quasi-affine pullback projection. -/
theorem iff_existsEtaleOnTarget : QuasiAffine f ↔ existsEtaleOnTarget f :=
  (tfae f).out 1 2

/-- A morphism of algebraic spaces is quasi-affine iff some Zariski covering of
the target has quasi-affine inverse images under `f`. -/
theorem iff_existsZariskiCover : QuasiAffine f ↔ existsZariskiCover f := (tfae f).out 1 3

/-- A quasi-affine morphism of algebraic spaces is relatively representable. -/
theorem relativelyRepresentable [QuasiAffine f] :
    yoneda.relativelyRepresentable f := ((iff_over_presheaf f).mp inferInstance).rep

end QuasiAffine

end AlgebraicGeometry.AlgebraicSpace
