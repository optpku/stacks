module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap65.Definition_65_12_5_ZariskiCover
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree

/-!
# Characterizations of finite locally free morphisms of algebraic spaces

A morphism of algebraic spaces is finite locally free iff it is representable
and finite locally free, iff some surjective étale scheme atlas has finite
locally free projection, and iff some Zariski covering of the target has finite
locally free inverse images.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FiniteLocallyFree

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- `f` is representable and finite locally free in the Section 67.3 sense: it is
`yoneda.relativelyRepresentable` and `(over IsFiniteLocallyFree).presheaf`. -/
def representable : Prop :=
  yoneda.relativelyRepresentable f ∧
    (over (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})).presheaf f

/-- `representable f` means `f` is relatively representable and finite locally
free as a presheaf morphism in the sense of Section 67.3. -/
theorem representable_iff : representable f ↔
    yoneda.relativelyRepresentable f ∧
      (over (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

namespace representable

/-- Relative representability together with the Section 67.3 finite locally free
presheaf condition witnesses `representable f`. -/
theorem of (hf : yoneda.relativelyRepresentable f)
    (h : (over (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})).presheaf f) :
    representable f := sorry

/-- `representable f` supplies relative representability and the Section 67.3
finite locally free presheaf condition. -/
theorem spec (h : representable f) :
    yoneda.relativelyRepresentable f ∧
      (over (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

end representable

/-- There exists a scheme `V` and a surjective étale morphism `V ⟶ Y` such that
`V ×_Y X ⟶ V` is finite locally free. -/
def existsSurjectiveEtaleTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → FiniteLocallyFree pV

/-- `existsSurjectiveEtaleTarget f` is the existence of a surjective étale scheme
atlas of `Y` along which the projection `V ×_Y X ⟶ V` is finite locally free. -/
theorem existsSurjectiveEtaleTarget_iff : existsSurjectiveEtaleTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → FiniteLocallyFree pV := sorry

namespace existsSurjectiveEtaleTarget

/-- A surjective étale scheme atlas of `Y` with finite locally free pullback
projection of `f` witnesses `existsSurjectiveEtaleTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → FiniteLocallyFree pV) :
    existsSurjectiveEtaleTarget f := sorry

/-- `existsSurjectiveEtaleTarget f` supplies a surjective étale scheme atlas of
`Y` along which pullback projections of `f` are finite locally free. -/
theorem spec (h : existsSurjectiveEtaleTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → FiniteLocallyFree pV := sorry

end existsSurjectiveEtaleTarget

/-- There exists a Zariski covering `Y = ⋃ Yᵢ` such that each inverse-image
morphism `f⁻¹(Yᵢ) ⟶ Yᵢ` is finite locally free. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → FiniteLocallyFree pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` map in a finite locally free way to the covering
opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → FiniteLocallyFree pYi := sorry

namespace existsZariskiCover

/-- A Zariski covering of `Y` with finite locally free inverse-image projections
of `f` witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → FiniteLocallyFree pYi) :
    existsZariskiCover f := sorry

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map in a finite locally free way to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → FiniteLocallyFree pYi := sorry

end existsZariskiCover

end FiniteLocallyFree

end AlgebraicGeometry.AlgebraicSpace
