/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard
public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor

/-!
# Torsors under group schemes

This module defines cover-local triviality for a pseudo action of a group scheme and
specializes it to the fpqc and five standard scheme precoverages.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupScheme

variable {S : Scheme.{u}} (G : Grp (Over S)) (X : Mod (Over S) G.X)

/-- A pseudo `G`-torsor is trivial on a chosen cover when it has a section over every
member of the cover. -/
def IsTrivialOn {K : Precoverage Scheme.{u}} (U : S.Cover.{u} K) : Prop :=
  ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X)

/-- Triviality on a chosen cover is memberwise existence of sections. -/
theorem isTrivialOn_iff {K : Precoverage Scheme.{u}} (U : S.Cover.{u} K) :
    IsTrivialOn G X U ↔
      ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X) :=
  Iff.rfl

/-- A `G`-action is a torsor for `K` when it is a pseudo-torsor and is trivial on
some `K`-cover. -/
structure IsTorsorFor (K : Precoverage Scheme.{u}) : Prop where
  isPseudoTorsor : Mod.IsPseudoTorsor X
  exists_trivializingCover : ∃ U : S.Cover.{u} K, IsTrivialOn G X U

/-- Constructs a torsor for `K` from a pseudo-torsor and a chosen trivializing cover. -/
def IsTorsorFor.ofTrivializingCover {K : Precoverage Scheme.{u}}
    (hX : Mod.IsPseudoTorsor X) (U : S.Cover.{u} K) (hU : IsTrivialOn G X U) :
    IsTorsorFor G X K where
  isPseudoTorsor := hX
  exists_trivializingCover := ⟨U, hU⟩

/-- The cover-and-sections characterization of a torsor for a precoverage. -/
theorem isTorsorFor_iff (K : Precoverage Scheme.{u}) :
    IsTorsorFor G X K ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : S.Cover.{u} K,
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X) := by
  constructor
  · intro hX
    exact ⟨hX.isPseudoTorsor, hX.exists_trivializingCover⟩
  · rintro ⟨hX, hU⟩
    exact ⟨hX, hU⟩

/-- A torsor for a precoverage remains a torsor after enlarging the precoverage. -/
theorem IsTorsorFor.mono {K L : Precoverage Scheme.{u}} (hKL : K ≤ L)
    (hX : IsTorsorFor G X K) : IsTorsorFor G X L := by
  obtain ⟨U, hU⟩ := hX.exists_trivializingCover
  exact IsTorsorFor.ofTrivializingCover G X hX.isPseudoTorsor (U.weaken hKL) hU

/-- A pseudo `G`-torsor that acquires sections on an fpqc cover. -/
abbrev IsTorsor : Prop :=
  IsTorsorFor G X Scheme.fpqcPrecoverage

/-- The fpqc cover-and-sections characterization of a `G`-torsor. -/
theorem isTorsor_iff :
    IsTorsor G X ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : S.Cover.{u} Scheme.fpqcPrecoverage,
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X) :=
  isTorsorFor_iff G X Scheme.fpqcPrecoverage

/-- A pseudo `G`-torsor that acquires sections in the standard topology `τ`. -/
abbrev IsStandardTorsor (τ : StandardTopology) : Prop :=
  IsTorsorFor G X τ.precoverage

/-- The cover-and-sections characterization of a torsor for a standard topology. -/
theorem isStandardTorsor_iff (τ : StandardTopology) :
    IsStandardTorsor G X τ ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : S.Cover.{u} τ.precoverage,
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X) :=
  isTorsorFor_iff G X τ.precoverage

/-- An étale-locally trivial pseudo `G`-torsor. -/
abbrev IsQuasiIsotrivial : Prop :=
  IsStandardTorsor G X .etale

/-- The étale cover-and-sections characterization of quasi-isotriviality. -/
theorem isQuasiIsotrivial_iff :
    IsQuasiIsotrivial G X ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : S.Cover.{u} StandardTopology.etale.precoverage,
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X) :=
  isStandardTorsor_iff G X .etale

/-- A Zariski-locally trivial pseudo `G`-torsor. -/
abbrev IsLocallyTrivial : Prop :=
  IsStandardTorsor G X .zariski

/-- The Zariski cover-and-sections characterization of local triviality. -/
theorem isLocallyTrivial_iff :
    IsLocallyTrivial G X ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : S.Cover.{u} StandardTopology.zariski.precoverage,
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X) :=
  isStandardTorsor_iff G X .zariski

/-- The flatness and finite-presentation parts of syntomicity can be checked on the
affine neighborhoods in its definition. -/
private theorem syntomic_flat_and_locallyOfFinitePresentation
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) (hf : Syntomic f) :
    Flat f ∧ LocallyOfFinitePresentation f := by
  constructor
  · show Flat f
    rw [HasRingHomProperty.iff_exists_appLE (P := @Flat)
      (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.Flat.holdsForLocalizationAway).left]
    intro y
    obtain ⟨U, hy, V, e, h⟩ := hf.property y
    exact ⟨V, U, hy, e, h.1⟩
  · show LocallyOfFinitePresentation f
    rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
      (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.finitePresentation_holdsForLocalizationAway).left]
    intro y
    obtain ⟨U, hy, V, e, h⟩ := hf.property y
    exact ⟨V, U, hy, e, h.2.1⟩

/-- Every torsor for a standard topology is an fpqc torsor. -/
theorem IsStandardTorsor.isTorsor {τ : StandardTopology}
    (hX : IsStandardTorsor G X τ) : IsTorsor G X := by
  have hτ : τ.precoverage ≤ Scheme.fppfPrecoverage := by
    cases τ with
    | zariski => exact Scheme.zariskiPrecoverage_le_fppfPrecoverage
    | etale =>
      apply Scheme.precoverage_mono
      intro Y Z f hf
      exact ⟨(Etale.iff_flat_and_formallyUnramified.mp hf).1,
        (Etale.iff_flat_and_formallyUnramified.mp hf).2.2⟩
    | smooth =>
      apply Scheme.precoverage_mono
      intro Y Z f hf
      letI : Smooth f := hf
      refine ⟨⟨?_⟩, ⟨?_⟩⟩
      · intro V hV U hU e
        exact (f.smooth_appLE hV hU e).flat
      · intro V hV U hU e
        exact (f.smooth_appLE hV hU e).finitePresentation
    | syntomic =>
      exact Scheme.precoverage_mono fun _ _ f hf ↦
        syntomic_flat_and_locallyOfFinitePresentation f hf
    | fppf => exact le_rfl
  exact IsTorsorFor.mono G X
    (hτ.trans Scheme.fppfPrecoverage_le_fpqcPrecoverage) hX

/-- Every quasi-isotrivial pseudo torsor is an fpqc torsor. -/
theorem IsQuasiIsotrivial.isTorsor
    (hX : IsQuasiIsotrivial G X) : IsTorsor G X :=
  IsStandardTorsor.isTorsor G X hX

/-- Every Zariski-locally trivial pseudo torsor is an fpqc torsor. -/
theorem IsLocallyTrivial.isTorsor
    (hX : IsLocallyTrivial G X) : IsTorsor G X :=
  IsStandardTorsor.isTorsor G X hX

end AlgebraicGeometry.GroupScheme
