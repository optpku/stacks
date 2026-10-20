module

public import Mathlib.Data.List.TFAE
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic

/-!
# Characterizations of affine morphisms of algebraic spaces

A morphism of algebraic spaces is affine iff it is representable and affine,
iff étale pullbacks from affine schemes are affine, iff some surjective étale
scheme atlas has affine projection, and iff some Zariski covering of the target
has affine inverse images.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Affine

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- `f` is relatively representable and satisfies the affine presheaf morphism
property induced by affine morphisms of schemes. -/
def representableAffine : Prop :=
  yoneda.relativelyRepresentable f ∧
    (over (@IsAffineHom : MorphismProperty Scheme.{u})).presheaf f

/-- `representableAffine f` means `f` is relatively representable and affine as a
presheaf morphism. -/
theorem representableAffine_iff : representableAffine f ↔
    yoneda.relativelyRepresentable f ∧
      (over (@IsAffineHom : MorphismProperty Scheme.{u})).presheaf f := Iff.rfl

namespace representableAffine

/-- Relative representability together with the affine presheaf
condition witnesses `representableAffine f`. -/
theorem of (hf : yoneda.relativelyRepresentable f)
    (h : (over (@IsAffineHom : MorphismProperty Scheme.{u})).presheaf f) :
    representableAffine f := ⟨hf, h⟩

/-- `representableAffine f` supplies relative representability and the
affine presheaf condition. -/
theorem spec (h : representableAffine f) :
    yoneda.relativelyRepresentable f ∧
      (over (@IsAffineHom : MorphismProperty Scheme.{u})).presheaf f := h

end representableAffine

/-- For every affine scheme `V` and étale morphism `V ⟶ Y`, the fibre product
`X ×_Y V` is an affine algebraic space. -/
def forallAffineEtale : Prop :=
  ∀ {V : Over S} [AlgebraicGeometry.IsAffine V.left] {P : AlgebraicSpace S}
    {g : ofOver V ⟶ Y} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
    Etale g → IsPullback pV pX g f → IsAffine P

/-- `forallAffineEtale f` means every étale morphism from an affine scheme to `Y`
has affine fibre product with `X`. -/
theorem forallAffineEtale_iff : forallAffineEtale f ↔
    ∀ (V : Over S) [AlgebraicGeometry.IsAffine V.left] (P : AlgebraicSpace S)
      (g : ofOver V ⟶ Y) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
      Etale g → IsPullback pV pX g f → IsAffine P := Iff.rfl

namespace forallAffineEtale

/-- A universal étale affine-scheme pullback condition witnesses
`forallAffineEtale f`. -/
theorem of (h : ∀ {V : Over S} [AlgebraicGeometry.IsAffine V.left]
    {P : AlgebraicSpace S} {g : ofOver V ⟶ Y} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
    Etale g → IsPullback pV pX g f → IsAffine P) : forallAffineEtale f := h

/-- Under `forallAffineEtale f`, the vertex of any étale pullback of `f` from an
affine scheme is affine. -/
theorem spec (h : forallAffineEtale f) {V : Over S}
    [AlgebraicGeometry.IsAffine V.left] {P : AlgebraicSpace S}
    {g : ofOver V ⟶ Y} {pV : P ⟶ ofOver V} {pX : P ⟶ X} (hg : Etale g)
    (sq : IsPullback pV pX g f) : IsAffine P := h hg sq

end forallAffineEtale

/-- There exists a scheme `V` and a surjective étale morphism `V ⟶ Y` such that
`V ×_Y X ⟶ V` is affine. -/
def existsSurjectiveEtaleTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → Affine pV

/-- `existsSurjectiveEtaleTarget f` is the existence of a surjective étale scheme
atlas of `Y` along which the projection `V ×_Y X ⟶ V` is affine. -/
theorem existsSurjectiveEtaleTarget_iff : existsSurjectiveEtaleTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → Affine pV := Iff.rfl

namespace existsSurjectiveEtaleTarget

/-- A surjective étale scheme atlas of `Y` with affine pullback projection of
`f` witnesses `existsSurjectiveEtaleTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → Affine pV) : existsSurjectiveEtaleTarget f := ⟨V, ψ, inferInstance, inferInstance, h⟩

/-- `existsSurjectiveEtaleTarget f` supplies a surjective étale scheme atlas of
`Y` along which pullback projections of `f` are affine. -/
theorem spec (h : existsSurjectiveEtaleTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → Affine pV := h

end existsSurjectiveEtaleTarget

/-- There exists a Zariski covering `Y = ⋃ Yᵢ` such that each inverse-image
morphism `f⁻¹(Yᵢ) ⟶ Yᵢ` is affine. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Affine pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` map affinely to the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → Affine pYi := Iff.rfl

namespace existsZariskiCover

/-- A Zariski covering of `Y` with affine inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Affine pYi) :
    existsZariskiCover f := ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map affinely to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → Affine pYi := h

end existsZariskiCover

/-- For a morphism of algebraic spaces over a scheme, representable affineness,
affineness, affineness of all affine-scheme étale pullbacks, affineness after
some surjective étale scheme atlas, and affineness over some Zariski covering
of the target are equivalent. -/
theorem tfae :
    List.TFAE [representableAffine f, Affine f, forallAffineEtale f,
      existsSurjectiveEtaleTarget f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is affine iff it is representable and affine
as a presheaf morphism. -/
theorem iff_representableAffine : Affine f ↔ representableAffine f := (tfae f).out 1 0

/-- A morphism of algebraic spaces is affine iff every étale morphism from an
affine scheme to the target has affine fibre product. -/
theorem iff_forallAffineEtale : Affine f ↔ forallAffineEtale f := (tfae f).out 1 2

/-- A morphism of algebraic spaces is affine iff some surjective étale scheme
atlas of the target has affine pullback projection. -/
theorem iff_existsSurjectiveEtaleTarget :
    Affine f ↔ existsSurjectiveEtaleTarget f := (tfae f).out 1 3

/-- A morphism of algebraic spaces is affine iff some Zariski covering of the
target has affine inverse images under `f`. -/
theorem iff_existsZariskiCover : Affine f ↔ existsZariskiCover f := (tfae f).out 1 4

end Affine

end AlgebraicGeometry.AlgebraicSpace
