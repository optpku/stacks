/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType

/-!
# Finite presentation scheme morphisms

This file packages finite presentation of scheme morphisms from mathlib's local finite-presentation
condition together with quasi-compactness and quasi-separatedness. The pointwise affine API is
kept for arguments that need a chosen source point and affine neighborhoods.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A morphism `f : X ⟶ S` is of finite presentation at `x ∈ X` when `x` has affine source and
target neighborhoods on which the induced ring homomorphism is of finite presentation. -/
def FinitePresentationAt (x : X) : Prop :=
  ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
    ∃ V : S.affineOpens,
      ∃ e : U ≤ f ⁻¹ᵁ V,
        (CommRingCat.Hom.hom (f.appLE V U e)).FinitePresentation

/-- A `FinitePresentationAt` hypothesis supplies its affine-neighborhood witness. -/
theorem FinitePresentationAt.exists_affineNeighborhood
    {x : X} (hx : f.FinitePresentationAt x) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ V : S.affineOpens,
        ∃ e : U ≤ f ⁻¹ᵁ V,
          (CommRingCat.Hom.hom (f.appLE V U e)).FinitePresentation := sorry

/-- `FinitePresentationAt f x` is exactly its affine-neighborhood witness condition. -/
theorem finitePresentationAt_iff (x : X) :
    f.FinitePresentationAt x ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ V : S.affineOpens,
          ∃ e : U ≤ f ⁻¹ᵁ V,
            (CommRingCat.Hom.hom (f.appLE V U e)).FinitePresentation := sorry

/-- The pointwise affine-neighborhood formulation of finite presentation agrees with
`LocallyOfFinitePresentation`. -/
theorem locallyOfFinitePresentation_iff_locallyOfType :
    LocallyOfFinitePresentation f ↔ LocallyOfType RingHom.FinitePresentation f := sorry

/-- A scheme morphism is locally of finite presentation if and only if the target has an open
cover whose pullbacks have open covers by locally finitely presented morphisms. -/
theorem locallyOfFinitePresentation_iff_exists_openCover :
    LocallyOfFinitePresentation f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, LocallyOfFinitePresentation (𝒰.f i ≫ 𝒱.pullbackHom f j) := by
  constructor
  · intro hf
    have hf' : LocallyOfType RingHom.FinitePresentation f :=
      (Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType f).1 hf
    rcases (locallyOfType_iff_exists_openCover
      RingHom.FinitePresentation RingHom.finitePresentation_isLocal).1 hf' with
      ⟨𝒱, h𝒱⟩
    refine ⟨𝒱, ?_⟩
    intro j
    rcases h𝒱 j with ⟨𝒰, h𝒰⟩
    refine ⟨𝒰, ?_⟩
    intro i
    have h :
        LocallyOfFinitePresentation (𝒰.f i ≫ 𝒱.pullbackHom f j) ↔
          LocallyOfType RingHom.FinitePresentation (𝒰.f i ≫ 𝒱.pullbackHom f j) :=
      Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType
        (𝒰.f i ≫ 𝒱.pullbackHom f j)
    exact
      h.2 (h𝒰 i)
  · rintro ⟨𝒱, h𝒱⟩
    have h𝒱' :
        ∃ 𝒰 : S.OpenCover, ∀ j : 𝒰.I₀,
          ∃ 𝒲 : ((𝒰.pullback₁ f).X j).OpenCover,
            ∀ i : 𝒲.I₀,
              LocallyOfType RingHom.FinitePresentation (𝒲.f i ≫ 𝒰.pullbackHom f j) := by
      refine ⟨𝒱, ?_⟩
      intro j
      rcases h𝒱 j with ⟨𝒰, h𝒰⟩
      refine ⟨𝒰, ?_⟩
      intro i
      have h :
          LocallyOfFinitePresentation (𝒰.f i ≫ 𝒱.pullbackHom f j) ↔
            LocallyOfType RingHom.FinitePresentation (𝒰.f i ≫ 𝒱.pullbackHom f j) :=
        Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType
          (𝒰.f i ≫ 𝒱.pullbackHom f j)
      exact
        h.1 (h𝒰 i)
    exact
      (Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType f).2 <|
        (locallyOfType_iff_exists_openCover
          RingHom.FinitePresentation RingHom.finitePresentation_isLocal).2 h𝒱'

/-- A scheme morphism is locally of finite presentation if and only if the target has an affine
open cover whose pullbacks have affine open covers on which every induced map on global sections
is of finite presentation. -/
theorem locallyOfFinitePresentation_iff_exists_affineOpenCover :
    LocallyOfFinitePresentation f ↔
      ∃ 𝒱 : S.AffineOpenCover.{u}, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover.{u},
          ∀ i : 𝒰.I₀,
            RingHom.FinitePresentation (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom) := by
  have h :
      LocallyOfType RingHom.FinitePresentation f ↔
        ∃ 𝒱 : S.AffineOpenCover.{u}, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover.{u},
            ∀ i : 𝒰.I₀,
              RingHom.FinitePresentation (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom) :=
    locallyOfType_iff_exists_affineOpenCover
      RingHom.FinitePresentation RingHom.finitePresentation_isLocal
      (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.finitePresentation_holdsForLocalizationAway).left
  simpa [Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType f] using
    h

/-- A locally finitely presented morphism is locally of type `RingHom.FinitePresentation`. -/
instance instLocallyOfTypeRingHomFinitePresentationOfLocallyOfFinitePresentation
    [LocallyOfFinitePresentation f] :
    LocallyOfType RingHom.FinitePresentation f :=
  (locallyOfFinitePresentation_iff_locallyOfType f).mp inferInstance

/-- A morphism is locally of finite presentation exactly when it is of finite presentation at
every source point. -/
theorem locallyOfFinitePresentation_iff_forall_finitePresentationAt :
    LocallyOfFinitePresentation f ↔ ∀ x : X, f.FinitePresentationAt x := sorry

/-- A scheme morphism is of finite presentation when it is locally of finite presentation,
quasi-compact, and quasi-separated. -/
class FinitePresentation : Prop extends
    LocallyOfFinitePresentation f,
    QuasiCompact f,
    QuasiSeparated f

/-- Local finite presentation, quasi-compactness, and quasi-separatedness canonically give finite
presentation. -/
instance instFinitePresentation
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    FinitePresentation f where
  toLocallyOfFinitePresentation := inferInstance
  toQuasiCompact := inferInstance
  toQuasiSeparated := inferInstance

/-- A morphism of finite presentation is locally of finite presentation. -/
instance instLocallyOfFinitePresentationOfFinitePresentation [h : FinitePresentation f] :
    LocallyOfFinitePresentation f :=
  h.toLocallyOfFinitePresentation

/-- A morphism of finite presentation is quasi-compact. -/
instance instQuasiCompactOfFinitePresentation [h : FinitePresentation f] :
    QuasiCompact f :=
  h.toQuasiCompact

/-- A morphism of finite presentation is quasi-separated. -/
instance instQuasiSeparatedOfFinitePresentation [h : FinitePresentation f] :
    QuasiSeparated f :=
  h.toQuasiSeparated

/-- `FinitePresentation f` is equivalent to local finite presentation, quasi-compactness, and
quasi-separatedness. -/
theorem finitePresentation_iff :
    FinitePresentation f ↔
      LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f := sorry

/-- `FinitePresentation f` is equivalent to quasi-compactness, quasi-separatedness, and finite
presentation at every source point. -/
theorem FinitePresentation.iff_forall_at :
    FinitePresentation f ↔
      QuasiCompact f ∧ QuasiSeparated f ∧ ∀ x : X, f.FinitePresentationAt x := sorry

/-- The image of a locally constructible set under a quasi-compact, locally finitely presented
morphism of schemes is locally constructible. -/
theorem chevalley [LocallyOfFinitePresentation f] [QuasiCompact f]
    {s : Set X} (hs : Topology.IsLocallyConstructible s) :
    Topology.IsLocallyConstructible (f '' s) := by
  exact f.isLocallyConstructible_image hs

end Scheme.Hom
end AlgebraicGeometry
