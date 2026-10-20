module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import Mathlib.Data.List.TFAE
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree

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

/-- The morphism is relatively representable and all its scheme base changes
are finite locally free. -/
def representable : Prop :=
  yoneda.relativelyRepresentable f ∧
    (over (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})).presheaf f

/-- `representable f` means `f` is relatively representable and finite locally
free as a presheaf morphism. -/
theorem representable_iff : representable f ↔
    yoneda.relativelyRepresentable f ∧
      (over (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})).presheaf f :=
  Iff.rfl

namespace representable

/-- Relative representability together with the finite locally free
presheaf condition witnesses `representable f`. -/
theorem of (hf : yoneda.relativelyRepresentable f)
    (h : (over (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})).presheaf f) :
    representable f := ⟨hf, h⟩

/-- `representable f` supplies relative representability and the
finite locally free presheaf condition. -/
theorem spec (h : representable f) :
    yoneda.relativelyRepresentable f ∧
      (over (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})).presheaf f :=
  h

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
          IsPullback pV pX ψ f → FiniteLocallyFree pV := Iff.rfl

namespace existsSurjectiveEtaleTarget

/-- A surjective étale scheme atlas of `Y` with finite locally free pullback
projection of `f` witnesses `existsSurjectiveEtaleTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → FiniteLocallyFree pV) :
    existsSurjectiveEtaleTarget f := ⟨V, ψ, inferInstance, inferInstance, h⟩

/-- `existsSurjectiveEtaleTarget f` supplies a surjective étale scheme atlas of
`Y` along which pullback projections of `f` are finite locally free. -/
theorem spec (h : existsSurjectiveEtaleTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → FiniteLocallyFree pV := h

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
        IsPullback pYi pX (𝒰.f i) f → FiniteLocallyFree pYi := Iff.rfl

namespace existsZariskiCover

/-- A Zariski covering of `Y` with finite locally free inverse-image projections
of `f` witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → FiniteLocallyFree pYi) :
    existsZariskiCover f := ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map in a finite locally free way to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → FiniteLocallyFree pYi := h

end existsZariskiCover

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `f` is representable and finite locally free;
`FiniteLocallyFree f`; some scheme `V` with a surjective étale morphism `V ⟶ Y`
has `V ×_Y X ⟶ V` finite locally free; and some Zariski covering `Y = ⋃ Yᵢ` has
each inverse-image morphism `f⁻¹(Yᵢ) ⟶ Yᵢ` finite locally free. -/
theorem tfae :
    List.TFAE [representable f, FiniteLocallyFree f, existsSurjectiveEtaleTarget f,
      existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is finite locally free iff it is representable
and finite locally free after every scheme base change. -/
theorem iff_representable : FiniteLocallyFree f ↔ representable f := (tfae f).out 1 0

/-- A morphism of algebraic spaces is finite locally free iff some surjective
étale scheme atlas of the target has finite locally free pullback projection. -/
theorem iff_existsSurjectiveEtaleTarget :
    FiniteLocallyFree f ↔ existsSurjectiveEtaleTarget f := (tfae f).out 1 2

/-- A morphism of algebraic spaces is finite locally free iff some Zariski
covering of the target has finite locally free inverse images under `f`. -/
theorem iff_existsZariskiCover :
    FiniteLocallyFree f ↔ existsZariskiCover f := (tfae f).out 1 3


end FiniteLocallyFree

end AlgebraicGeometry.AlgebraicSpace
