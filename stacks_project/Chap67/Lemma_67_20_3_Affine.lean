/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap65.Definition_65_12_5_ZariskiCover
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_20_2_Affine

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

/-- `f` is representable and affine in the Section 67.3 sense: it is
`yoneda.relativelyRepresentable` and `(over IsAffineHom).presheaf`. -/
def representableAffine : Prop :=
  yoneda.relativelyRepresentable f ∧
    (over (@IsAffineHom : MorphismProperty Scheme.{u})).presheaf f

/-- `representableAffine f` means `f` is relatively representable and affine as a
presheaf morphism in the sense of Section 67.3. -/
theorem representableAffine_iff : representableAffine f ↔
    yoneda.relativelyRepresentable f ∧
      (over (@IsAffineHom : MorphismProperty Scheme.{u})).presheaf f := sorry

namespace representableAffine

/-- Relative representability together with the Section 67.3 affine presheaf
condition witnesses `representableAffine f`. -/
theorem of (hf : yoneda.relativelyRepresentable f)
    (h : (over (@IsAffineHom : MorphismProperty Scheme.{u})).presheaf f) :
    representableAffine f := sorry

/-- `representableAffine f` supplies relative representability and the
Section 67.3 affine presheaf condition. -/
theorem spec (h : representableAffine f) :
    yoneda.relativelyRepresentable f ∧
      (over (@IsAffineHom : MorphismProperty Scheme.{u})).presheaf f := sorry

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
      Etale g → IsPullback pV pX g f → IsAffine P := sorry

namespace forallAffineEtale

/-- A universal étale affine-scheme pullback condition witnesses
`forallAffineEtale f`. -/
theorem of (h : ∀ {V : Over S} [AlgebraicGeometry.IsAffine V.left]
    {P : AlgebraicSpace S} {g : ofOver V ⟶ Y} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
    Etale g → IsPullback pV pX g f → IsAffine P) : forallAffineEtale f := sorry

/-- Under `forallAffineEtale f`, the vertex of any étale pullback of `f` from an
affine scheme is affine. -/
theorem spec (h : forallAffineEtale f) {V : Over S}
    [AlgebraicGeometry.IsAffine V.left] {P : AlgebraicSpace S}
    {g : ofOver V ⟶ Y} {pV : P ⟶ ofOver V} {pX : P ⟶ X} (hg : Etale g)
    (sq : IsPullback pV pX g f) : IsAffine P := sorry

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
          IsPullback pV pX ψ f → Affine pV := sorry

namespace existsSurjectiveEtaleTarget

/-- A surjective étale scheme atlas of `Y` with affine pullback projection of
`f` witnesses `existsSurjectiveEtaleTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → Affine pV) : existsSurjectiveEtaleTarget f := sorry

/-- `existsSurjectiveEtaleTarget f` supplies a surjective étale scheme atlas of
`Y` along which pullback projections of `f` are affine. -/
theorem spec (h : existsSurjectiveEtaleTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → Affine pV := sorry

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
        IsPullback pYi pX (𝒰.f i) f → Affine pYi := sorry

namespace existsZariskiCover

/-- A Zariski covering of `Y` with affine inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Affine pYi) :
    existsZariskiCover f := sorry

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map affinely to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → Affine pYi := sorry

end existsZariskiCover

/-- The chosen fibre product of an affine morphism with an étale morphism from
an affine scheme is an affine algebraic space. -/
theorem pullback_snd_ofOver_affine_etale {V : Over S}
    [AlgebraicGeometry.IsAffine V.left] [Affine f] (g : ofOver V ⟶ Y) [Etale g]
    [HasPullback f g] : IsAffine (pullback f g) := sorry

/-- The chosen pullback projection `pullback.snd f g` along an étale morphism
from a scheme is affine whenever `f` is affine. -/
theorem pullback_snd_ofOver_etale {V : Over S} [Affine f] (g : ofOver V ⟶ Y)
    [Etale g] [HasPullback f g] : Affine (pullback.snd f g) := sorry

end Affine

end AlgebraicGeometry.AlgebraicSpace
