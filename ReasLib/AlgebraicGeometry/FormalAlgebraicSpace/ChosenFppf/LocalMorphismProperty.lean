/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.WAdmCount
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.EtaleCover
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalTypes
public import ReasLib.RingTheory.Topology.LocalMorphismProperty

/-!
# Local properties of formal algebraic space morphisms

Local properties of continuous maps of countably indexed weakly admissible
rings have equivalent universal affine-chart, target-cover, and source-cover
tests on locally countably indexed formal algebraic spaces.
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

variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y)

/-- Every commutative square of `f` against étale maps from affine formal
algebraic spaces has top arrow corresponding to a morphism of `WAdm^count`
with property `P`. -/
def etaleAffineLocally : Prop :=
  ∀ {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V],
    ChosenBigFppfSite.etale pU →
      ChosenBigFppfSite.etale pV →
      CommSq q pU pV f → correspondsTo P q

/-- `etaleAffineLocally P f` means every étale affine-chart square over `f`
has top arrow corresponding to a morphism of `WAdm^count` with property `P`. -/
theorem etaleAffineLocally_iff : etaleAffineLocally P f ↔
    ∀ (U V : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
      [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V],
      ChosenBigFppfSite.etale pU →
        ChosenBigFppfSite.etale pV →
        CommSq q pU pV f → correspondsTo P q :=
  sorry

namespace etaleAffineLocally

/-- A universal étale affine-chart correspondence witnesses
`etaleAffineLocally P f`. -/
theorem of (h : ∀ {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V],
    ChosenBigFppfSite.etale pU →
      ChosenBigFppfSite.etale pV →
      CommSq q pU pV f → correspondsTo P q) :
    etaleAffineLocally P f := sorry

/-- `etaleAffineLocally P f` tests `P` on the top arrow of every étale affine
chart square over `f`. -/
theorem spec (h : etaleAffineLocally P f)
    {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V]
    (hEtU : ChosenBigFppfSite.etale pU)
    (hEtV : ChosenBigFppfSite.etale pV)
    (sq : CommSq q pU pV f) :
    correspondsTo P q := sorry

end etaleAffineLocally

/-- There is an affine étale covering `{Y_ j ⟶ Y}` such that each fibre
product `Y_ j ×_Y X` admits an affine étale covering `{X_ ji ⟶ Y_ j ×_Y X}`
with each `X_ ji ⟶ Y_ j` corresponding to a morphism of `WAdm^count` with
property `P`. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ j, Y_ j ⟶ Y),
    ChosenBigFppfSite.IsEtaleAffineCover π ∧
      ∀ j, ∃ (ι' : Type (max u v))
        (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (σ : ∀ k, X_ k ⟶ pullback (π j) f),
        ChosenBigFppfSite.IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f)

/-- `existsCoverOnTarget P f` unpacks as an affine étale covering of `Y`
and, for each chart, an affine étale covering of the fibre product with
`X` whose projections to the chart correspond to morphisms of `WAdm^count`
with property `P`. -/
theorem existsCoverOnTarget_iff : existsCoverOnTarget P f ↔
    ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ j, Y_ j ⟶ Y),
      ChosenBigFppfSite.IsEtaleAffineCover π ∧
        ∀ j, ∃ (ι' : Type (max u v))
          (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f),
          ChosenBigFppfSite.IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f) :=
  sorry

namespace existsCoverOnTarget

/-- An affine étale covering of `Y`, together with affine étale
coverings of each `Y_ j ×_Y X` whose projections to `Y_ j` correspond to
morphisms of `WAdm^count` with property `P`, witnesses
`existsCoverOnTarget P f`. -/
theorem of {ι : Type (max u v)}
    {Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ j, Y_ j ⟶ Y) (hY : ChosenBigFppfSite.IsEtaleAffineCover π)
    (hX : ∀ j, ∃ (ι' : Type (max u v))
      (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (σ : ∀ k, X_ k ⟶ pullback (π j) f),
      ChosenBigFppfSite.IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f)) :
    existsCoverOnTarget P f := sorry

/-- `existsCoverOnTarget P f` supplies an affine étale covering of `Y`
and compatible affine étale coverings of the fibre products with `X`. -/
theorem spec (h : existsCoverOnTarget P f) :
    ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ j, Y_ j ⟶ Y),
      ChosenBigFppfSite.IsEtaleAffineCover π ∧
        ∀ j, ∃ (ι' : Type (max u v))
          (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f),
          ChosenBigFppfSite.IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f) :=
  sorry

end existsCoverOnTarget

/-- There is an affine étale covering `{X_ i ⟶ X}` such that each chart
factors as `X_ i ⟶ Y_ i ⟶ Y` with `Y_ i` an affine formal algebraic space,
`Y_ i ⟶ Y` representable by algebraic spaces and étale, and `X_ i ⟶ Y_ i`
corresponding to a morphism of `WAdm^count` with property `P`. -/
def existsCoverOnSource : Prop :=
  ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ i, X_ i ⟶ X),
    ChosenBigFppfSite.IsEtaleAffineCover π ∧
      ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
        IsAffineFormalAlgebraicSpace Y_i ∧
          ChosenBigFppfSite.etale p ∧
            π i ≫ f = q ≫ p ∧ correspondsTo P q

/-- `existsCoverOnSource P f` unpacks as an affine étale covering of `X`
whose charts factor through affine étale charts of `Y` by morphisms
corresponding to morphisms of `WAdm^count` with property `P`. -/
theorem existsCoverOnSource_iff : existsCoverOnSource P f ↔
    ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X),
      ChosenBigFppfSite.IsEtaleAffineCover π ∧
        ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          IsAffineFormalAlgebraicSpace Y_i ∧
            ChosenBigFppfSite.etale p ∧
              π i ≫ f = q ≫ p ∧ correspondsTo P q :=
  sorry

namespace existsCoverOnSource

/-- An affine étale covering of `X` with affine étale factorizations
through `Y` corresponding to morphisms of `WAdm^count` with property `P`
witnesses `existsCoverOnSource P f`. -/
theorem of {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ i, X_ i ⟶ X) (hX : ChosenBigFppfSite.IsEtaleAffineCover π)
    (hFac : ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      IsAffineFormalAlgebraicSpace Y_i ∧
        ChosenBigFppfSite.etale p ∧
          π i ≫ f = q ≫ p ∧ correspondsTo P q) :
    existsCoverOnSource P f := sorry

/-- `existsCoverOnSource P f` supplies an affine étale covering of `X`
and affine étale factorizations through `Y`. -/
theorem spec (h : existsCoverOnSource P f) :
    ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X),
      ChosenBigFppfSite.IsEtaleAffineCover π ∧
        ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          IsAffineFormalAlgebraicSpace Y_i ∧
            ChosenBigFppfSite.etale p ∧
              π i ≫ f = q ≫ p ∧ correspondsTo P q :=
  sorry

end existsCoverOnSource

variable [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]

/-- For a local property of continuous morphisms of countably indexed weakly
admissible rings, universal testing on affine étale squares, testing on a
target cover and covers of its pullbacks, and testing on a source cover
factoring through affine étale target charts are equivalent. -/
theorem tfae (hP : IsLocalMorphismProperty P) :
    List.TFAE [etaleAffineLocally P f, existsCoverOnTarget P f,
      existsCoverOnSource P f] := sorry

/-- A local ring-morphism property holds on every affine étale square if and
only if it holds on a target cover and covers of its pullbacks. -/
theorem etaleAffineLocally_iff_existsCoverOnTarget
    (hP : IsLocalMorphismProperty P) :
    etaleAffineLocally P f ↔ existsCoverOnTarget P f := sorry

/-- A local ring-morphism property holds on every affine étale square if and
only if it holds on a source cover factoring through affine étale target
charts. -/
theorem etaleAffineLocally_iff_existsCoverOnSource
    (hP : IsLocalMorphismProperty P) :
    etaleAffineLocally P f ↔ existsCoverOnSource P f := sorry

end AlgebraicGeometry.IsLocallyCountablyIndexed
