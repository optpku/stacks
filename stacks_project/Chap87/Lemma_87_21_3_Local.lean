module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap87.Lemma_87_21_3_WAdm

/-!
# Étale affine tests of WAdm^count morphism properties

A local property `P` of morphisms of `WAdm^count` is tested on morphisms of
locally countably indexed formal algebraic spaces by every étale affine-chart
square, by some Definition 87.11.1 cover of the target and then of each fibre
product with the source, and by some Definition 87.11.1 cover of the source
factoring through affine étale charts of the target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

noncomputable section

universe u v

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop)

/-- A family `{X_ i ⟶ X}` is a covering as in Definition 87.11.1 when each
source is an affine formal algebraic space, each map is representable by
algebraic spaces and étale, and the coproduct map is locally surjective as a
map of sheaves. -/
structure IsEtaleAffineCover {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ i, X_ i ⟶ X) : Prop where
  /-- Each chart is an affine formal algebraic space. -/
  isAffine : ∀ i, IsAffineFormalAlgebraicSpace (X_ i)
  /-- Each chart map is representable by algebraic spaces. -/
  isRepresentable : ∀ i, representableByAlgebraicSpaces (π i)
  /-- Each chart map is relatively étale. -/
  isRelativelyEtale : ∀ i, relativelyEtale (π i)
  /-- The coproduct of the chart maps is locally surjective. -/
  isCover : ∃ (c : Cofan X_) (hc : IsColimit c),
    Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π)

namespace IsEtaleAffineCover

/-- Package a Definition 87.11.1 covering from affine étale charts whose
coproduct is locally surjective. -/
def of {ι : Type (max u v)} {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} {π : ∀ i, X_ i ⟶ X}
    (hAffine : ∀ i, IsAffineFormalAlgebraicSpace (X_ i))
    (hRep : ∀ i, representableByAlgebraicSpaces (π i))
    (hEtale : ∀ i, relativelyEtale (π i))
    (hCover : ∃ (c : Cofan X_) (hc : IsColimit c),
      Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π)) :
    IsEtaleAffineCover π where
  isAffine := hAffine
  isRepresentable := hRep
  isRelativelyEtale := hEtale
  isCover := hCover

/-- A family is a Definition 87.11.1 covering iff its objects are affine
formal algebraic spaces, its maps are representable by algebraic spaces and
étale, and the coproduct is locally surjective. -/
theorem iff {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} (π : ∀ i, X_ i ⟶ X) :
    IsEtaleAffineCover π ↔
      (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i, relativelyEtale (π i)) ∧
            ∃ (c : Cofan X_) (hc : IsColimit c),
              Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) :=
  sorry

/-- A Definition 87.11.1 covering unpacks as affine sources, étale chart maps,
and a locally surjective coproduct. -/
theorem spec {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} {π : ∀ i, X_ i ⟶ X}
    (h : IsEtaleAffineCover π) :
    (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
      (∀ i, representableByAlgebraicSpaces (π i)) ∧
        (∀ i, relativelyEtale (π i)) ∧
          ∃ (c : Cofan X_) (hc : IsColimit c),
            Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) :=
  sorry

end IsEtaleAffineCover

variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y)

/-- Every commutative square of `f` against étale maps from affine formal
algebraic spaces has top arrow corresponding to a morphism of `WAdm^count`
with property `P`. This is condition (1) of Lemma 87.21.3. -/
def etaleAffineLocally : Prop :=
  ∀ {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V],
    representableByAlgebraicSpaces pU → relativelyEtale pU →
      representableByAlgebraicSpaces pV → relativelyEtale pV →
      CommSq q pU pV f → correspondsTo P q

/-- `etaleAffineLocally P f` means every étale affine-chart square over `f`
has top arrow corresponding to a morphism of `WAdm^count` with property `P`. -/
theorem etaleAffineLocally_iff : etaleAffineLocally P f ↔
    ∀ (U V : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
      [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V],
      representableByAlgebraicSpaces pU → relativelyEtale pU →
        representableByAlgebraicSpaces pV → relativelyEtale pV →
        CommSq q pU pV f → correspondsTo P q :=
  sorry

namespace etaleAffineLocally

/-- A universal étale affine-chart correspondence witnesses
`etaleAffineLocally P f`. -/
theorem of (h : ∀ {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V],
    representableByAlgebraicSpaces pU → relativelyEtale pU →
      representableByAlgebraicSpaces pV → relativelyEtale pV →
      CommSq q pU pV f → correspondsTo P q) :
    etaleAffineLocally P f := sorry

/-- `etaleAffineLocally P f` tests `P` on the top arrow of every étale affine
chart square over `f`. -/
theorem spec (h : etaleAffineLocally P f)
    {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V]
    (hRepU : representableByAlgebraicSpaces pU) (hEtU : relativelyEtale pU)
    (hRepV : representableByAlgebraicSpaces pV) (hEtV : relativelyEtale pV)
    (sq : CommSq q pU pV f) :
    correspondsTo P q := sorry

end etaleAffineLocally

/-- There is a Definition 87.11.1 covering `{Y_ j ⟶ Y}` such that each fibre
product `Y_ j ×_Y X` admits a Definition 87.11.1 covering `{X_ ji ⟶ Y_ j ×_Y X}`
with each `X_ ji ⟶ Y_ j` corresponding to a morphism of `WAdm^count` with
property `P`. This is condition (2) of Lemma 87.21.3. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ j, Y_ j ⟶ Y),
    IsEtaleAffineCover π ∧
      ∀ j, ∃ (ι' : Type (max u v))
        (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (σ : ∀ k, X_ k ⟶ pullback (π j) f),
        IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f)

/-- `existsCoverOnTarget P f` unpacks as a Definition 87.11.1 covering of `Y`
and, for each chart, a Definition 87.11.1 covering of the fibre product with
`X` whose projections to the chart correspond to morphisms of `WAdm^count`
with property `P`. -/
theorem existsCoverOnTarget_iff : existsCoverOnTarget P f ↔
    ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ j, Y_ j ⟶ Y),
      IsEtaleAffineCover π ∧
        ∀ j, ∃ (ι' : Type (max u v))
          (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f),
          IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f) :=
  sorry

namespace existsCoverOnTarget

/-- A Definition 87.11.1 covering of `Y`, together with Definition 87.11.1
coverings of each `Y_ j ×_Y X` whose projections to `Y_ j` correspond to
morphisms of `WAdm^count` with property `P`, witnesses
`existsCoverOnTarget P f`. -/
theorem of {ι : Type (max u v)}
    {Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ j, Y_ j ⟶ Y) (hY : IsEtaleAffineCover π)
    (hX : ∀ j, ∃ (ι' : Type (max u v))
      (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (σ : ∀ k, X_ k ⟶ pullback (π j) f),
      IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f)) :
    existsCoverOnTarget P f := sorry

/-- `existsCoverOnTarget P f` supplies a Definition 87.11.1 covering of `Y`
and compatible Definition 87.11.1 coverings of the fibre products with `X`. -/
theorem spec (h : existsCoverOnTarget P f) :
    ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ j, Y_ j ⟶ Y),
      IsEtaleAffineCover π ∧
        ∀ j, ∃ (ι' : Type (max u v))
          (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f),
          IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f) :=
  sorry

end existsCoverOnTarget

/-- There is a Definition 87.11.1 covering `{X_ i ⟶ X}` such that each chart
factors as `X_ i ⟶ Y_ i ⟶ Y` with `Y_ i` an affine formal algebraic space,
`Y_ i ⟶ Y` representable by algebraic spaces and étale, and `X_ i ⟶ Y_ i`
corresponding to a morphism of `WAdm^count` with property `P`. This is
condition (3) of Lemma 87.21.3. -/
def existsCoverOnSource : Prop :=
  ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ i, X_ i ⟶ X),
    IsEtaleAffineCover π ∧
      ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
        IsAffineFormalAlgebraicSpace Y_i ∧
          representableByAlgebraicSpaces p ∧ relativelyEtale p ∧
            π i ≫ f = q ≫ p ∧ correspondsTo P q

/-- `existsCoverOnSource P f` unpacks as a Definition 87.11.1 covering of `X`
whose charts factor through affine étale charts of `Y` by morphisms
corresponding to morphisms of `WAdm^count` with property `P`. -/
theorem existsCoverOnSource_iff : existsCoverOnSource P f ↔
    ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X),
      IsEtaleAffineCover π ∧
        ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          IsAffineFormalAlgebraicSpace Y_i ∧
            representableByAlgebraicSpaces p ∧ relativelyEtale p ∧
              π i ≫ f = q ≫ p ∧ correspondsTo P q :=
  sorry

namespace existsCoverOnSource

/-- A Definition 87.11.1 covering of `X` with affine étale factorizations
through `Y` corresponding to morphisms of `WAdm^count` with property `P`
witnesses `existsCoverOnSource P f`. -/
theorem of {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ i, X_ i ⟶ X) (hX : IsEtaleAffineCover π)
    (hFac : ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      IsAffineFormalAlgebraicSpace Y_i ∧
        representableByAlgebraicSpaces p ∧ relativelyEtale p ∧
          π i ≫ f = q ≫ p ∧ correspondsTo P q) :
    existsCoverOnSource P f := sorry

/-- `existsCoverOnSource P f` supplies a Definition 87.11.1 covering of `X`
and affine étale factorizations through `Y`. -/
theorem spec (h : existsCoverOnSource P f) :
    ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X),
      IsEtaleAffineCover π ∧
        ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          IsAffineFormalAlgebraicSpace Y_i ∧
            representableByAlgebraicSpaces p ∧ relativelyEtale p ∧
              π i ≫ f = q ≫ p ∧ correspondsTo P q :=
  sorry

end existsCoverOnSource

end AlgebraicGeometry.IsLocallyCountablyIndexed
