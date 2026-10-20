module

public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.Topology.AdicStar.LocalMorphismProperty
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Adic
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.EtaleCover

/-!
# Local morphism properties of locally adic-star formal algebraic spaces

Continuous homomorphism properties of adic-star rings can be tested on affine
étale charts, on target covers and their pullbacks, or on source covers
factoring through affine étale target charts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

noncomputable section

universe u v

namespace AlgebraicGeometry.IsLocallyAdicStar

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop)

/-- A morphism of affine formal algebraic spaces corresponds to a morphism of
`WAdm^{adic*}` with property `P` when there are adic* presentations of source
and target, together with a continuous ring map `φ` satisfying `P`, such that
`f` is identified with `Spf(φ)` on adic power stages. -/
def correspondsTo {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : U ⟶ V) : Prop :=
  ∃ (A B : Type u)
    (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsAdicStarRing A)
    (_ : CommRing B) (_ : TopologicalSpace B) (_ : IsAdicStarRing B)
    (φ : B →+* A) (_ : Continuous φ) (I : Ideal A) (J : Ideal B),
    P φ ∧ IsColimitMapOf φ I J f

/-- `correspondsTo P f` unpacks as adic* presentations of the affine source and
target together with a continuous ring map `φ` satisfying `P` that induces `f`
on adic power stages. -/
theorem correspondsTo_iff {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : U ⟶ V) :
    correspondsTo P f ↔
      ∃ (A B : Type u)
        (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsAdicStarRing A)
        (_ : CommRing B) (_ : TopologicalSpace B) (_ : IsAdicStarRing B)
        (φ : B →+* A) (_ : Continuous φ) (I : Ideal A) (J : Ideal B),
        P φ ∧ IsColimitMapOf φ I J f := sorry

namespace correspondsTo

variable {P}

/-- A continuous ring map `φ` with `P φ`, together with compatible `Spf`
presentations of the affine source and target, witnesses `correspondsTo P f`. -/
theorem of {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : U ⟶ V}
    {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
    (φ : B →+* A) (hφ : Continuous φ) (I : Ideal A) (J : Ideal B)
    (hPφ : P φ) (hinduces : IsColimitMapOf φ I J f) :
    correspondsTo P f := sorry

/-- `correspondsTo P f` supplies adic* presentations and a continuous ring map
`φ` with `P φ` inducing `f`. -/
theorem spec {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : U ⟶ V}
    (h : correspondsTo P f) :
    ∃ (A B : Type u)
      (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsAdicStarRing A)
      (_ : CommRing B) (_ : TopologicalSpace B) (_ : IsAdicStarRing B)
      (φ : B →+* A) (_ : Continuous φ) (I : Ideal A) (J : Ideal B),
      P φ ∧ IsColimitMapOf φ I J f := sorry

end correspondsTo

end AlgebraicGeometry.IsLocallyAdicStar

namespace AlgebraicGeometry.IsLocallyAdicStar

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop)
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y)

/-- Every commutative square of `f` against étale maps from affine formal
algebraic spaces has top arrow corresponding to a morphism of `WAdm^{adic*}`
with property `P`. -/
def etaleAffineLocally : Prop :=
  ∀ {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V],
    ChosenBigFppfSite.etale pU →
      ChosenBigFppfSite.etale pV →
      CommSq q pU pV f → correspondsTo P q

/-- `etaleAffineLocally P f` means every étale affine-chart square over `f`
has top arrow corresponding to a morphism of `WAdm^{adic*}` with property
`P`. -/
theorem etaleAffineLocally_iff : etaleAffineLocally P f ↔
    ∀ (U V : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
      [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V],
      ChosenBigFppfSite.etale pU →
        ChosenBigFppfSite.etale pV →
        CommSq q pU pV f → correspondsTo P q := sorry

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
with each `X_ ji ⟶ Y_ j` corresponding to a morphism of `WAdm^{adic*}` with
property `P`. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ j, Y_ j ⟶ Y),
    IsEtaleAffineCover π ∧
      ∀ j, ∃ (ι' : Type (max u v))
        (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (σ : ∀ k, X_ k ⟶ pullback (π j) f),
        IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f)

/-- `existsCoverOnTarget P f` unpacks as an affine étale covering of `Y`
and, for each chart, an affine étale covering of the fibre product with
`X` whose projections to the chart correspond to morphisms of `WAdm^{adic*}`
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

/-- An affine étale covering of `Y`, together with affine étale
coverings of each `Y_ j ×_Y X` whose projections to `Y_ j` correspond to
morphisms of `WAdm^{adic*}` with property `P`, witnesses
`existsCoverOnTarget P f`. -/
theorem of {ι : Type (max u v)}
    {Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ j, Y_ j ⟶ Y) (hY : IsEtaleAffineCover π)
    (hX : ∀ j, ∃ (ι' : Type (max u v))
      (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (σ : ∀ k, X_ k ⟶ pullback (π j) f),
      IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f)) :
    existsCoverOnTarget P f := sorry

/-- `existsCoverOnTarget P f` supplies an affine étale covering of `Y`
and compatible affine étale coverings of the fibre products with `X`. -/
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

/-- There is an affine étale covering `{X_ i ⟶ X}` such that each chart
factors as `X_ i ⟶ Y_ i ⟶ Y` with `Y_ i` an affine formal algebraic space,
`Y_ i ⟶ Y` representable by algebraic spaces and étale, and `X_ i ⟶ Y_ i`
corresponding to a morphism of `WAdm^{adic*}` with property `P`. -/
def existsCoverOnSource : Prop :=
  ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ i, X_ i ⟶ X),
    IsEtaleAffineCover π ∧
      ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
        IsAffineFormalAlgebraicSpace Y_i ∧
          ChosenBigFppfSite.etale p ∧
            π i ≫ f = q ≫ p ∧ correspondsTo P q

/-- `existsCoverOnSource P f` unpacks as an affine étale covering of `X`
whose charts factor through affine étale charts of `Y` by morphisms
corresponding to morphisms of `WAdm^{adic*}` with property `P`. -/
theorem existsCoverOnSource_iff : existsCoverOnSource P f ↔
    ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X),
      IsEtaleAffineCover π ∧
        ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          IsAffineFormalAlgebraicSpace Y_i ∧
            ChosenBigFppfSite.etale p ∧
              π i ≫ f = q ≫ p ∧ correspondsTo P q := sorry

namespace existsCoverOnSource

/-- An affine étale covering of `X` with affine étale factorizations
through `Y` corresponding to morphisms of `WAdm^{adic*}` with property `P`
witnesses `existsCoverOnSource P f`. -/
theorem of {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ i, X_ i ⟶ X) (hX : IsEtaleAffineCover π)
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
      IsEtaleAffineCover π ∧
        ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          IsAffineFormalAlgebraicSpace Y_i ∧
            ChosenBigFppfSite.etale p ∧
              π i ≫ f = q ≫ p ∧ correspondsTo P q := sorry

end existsCoverOnSource

end AlgebraicGeometry.IsLocallyAdicStar

namespace AlgebraicGeometry.IsLocallyAdicStar

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyAdicStar X] [IsLocallyAdicStar Y]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop)
variable (f : X ⟶ Y)

/-- Universal affine étale testing, target-cover testing, and source-cover testing
are equivalent for a local property of continuous homomorphisms of adic-star rings
on a size-closed chosen big fppf site. -/
theorem tfae (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮) (hP : IsAdicStarRing.IsLocalMorphismProperty P) :
    List.TFAE [etaleAffineLocally P f, existsCoverOnTarget P f,
      existsCoverOnSource P f] := sorry

/-- Universal affine étale testing is equivalent to testing on an affine étale
cover of the target and affine étale covers of its pullbacks to the source. -/
theorem etaleAffineLocally_iff_existsCoverOnTarget
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P) :
    etaleAffineLocally P f ↔ existsCoverOnTarget P f := sorry

/-- Universal affine étale testing is equivalent to testing on an affine étale
cover of the source factoring through affine étale charts of the target. -/
theorem etaleAffineLocally_iff_existsCoverOnSource
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P) :
    etaleAffineLocally P f ↔ existsCoverOnSource P f := sorry

end AlgebraicGeometry.IsLocallyAdicStar
