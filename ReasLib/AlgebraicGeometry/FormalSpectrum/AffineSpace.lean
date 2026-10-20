/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Morphism
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.McQuillan
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion
public import ReasLib.RingTheory.RestrictedPowerSeries.WeaklyAdmissible

/-!
# Affine spaces over formal spectra

Finite-dimensional affine spaces over formal spectra are formal spectra of
restricted power series, with their coefficient-induced projections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The structure morphism `Spec(RestrictedPowerSeries (Fin r) A) ⟶ S`. -/
def restrictedPowerSeriesSpecHom {S : Scheme.{u}} {A : Type u}
    [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) (r : ℕ) :
    Spec (.of (RestrictedPowerSeries (Fin r) A)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap A (RestrictedPowerSeries (Fin r) A))) ≫ hA

/-- Unfolding of `restrictedPowerSeriesSpecHom` as the composite of `Spec.map`
of the coefficient algebra map with the structure morphism of `A`. -/
theorem restrictedPowerSeriesSpecHom_eq {S : Scheme.{u}} {A : Type u}
    [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) (r : ℕ) :
    restrictedPowerSeriesSpecHom hA r =
      Spec.map (CommRingCat.ofHom (algebraMap A (RestrictedPowerSeries (Fin r) A))) ≫
        hA :=
  rfl

/-- Affine `r`-space over `Spf(A)`, as `Spf` of restricted power series
`RestrictedPowerSeries (Fin r) A`. -/
def affineSpace {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) (r : ℕ)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  spf (RestrictedPowerSeries (Fin r) A) (restrictedPowerSeriesSpecHom hA r)

/-- Unfolding of `affineSpace` as `Spf` of restricted power series. -/
theorem affineSpace_eq {S : Scheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) (r : ℕ)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    affineSpace hA r =
      spf (RestrictedPowerSeries (Fin r) A) (restrictedPowerSeriesSpecHom hA r) :=
  rfl

/-- The structure morphism `affineSpace hA r ⟶ Spf(A)` induced by the
coefficient algebra map. -/
def affineSpace.proj {S : Scheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) (r : ℕ)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    affineSpace hA r ⟶ spf A hA :=
  spfMap (algebraMap A (RestrictedPowerSeries (Fin r) A))
    (continuous_algebraMap A (RestrictedPowerSeries (Fin r) A))
    (restrictedPowerSeriesSpecHom_eq hA r).symm

/-- Unfolding of `affineSpace.proj` as `spfMap` of the coefficient algebra
map. -/
theorem affineSpace.proj_eq {S : Scheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) (r : ℕ)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    affineSpace.proj hA r =
      spfMap (algebraMap A (RestrictedPowerSeries (Fin r) A))
        (continuous_algebraMap A (RestrictedPowerSeries (Fin r) A))
        (restrictedPowerSeriesSpecHom_eq hA r).symm :=
  rfl

/-- Affine `r`-space over a McQuillan affine formal spectrum is McQuillan
affine. -/
instance instIsMcQuillanAffine_affineSpace {S : Scheme.{u}} {A : Type u}
    [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) (r : ℕ)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    IsMcQuillanAffine (affineSpace hA r).obj :=
  sorry

/-- A finite-type morphism from a McQuillan affine formal algebraic space to a
formal spectrum factors through a closed immersion into a finite-dimensional
affine space followed by its canonical projection. -/
theorem exists_closedImmersion_affineSpace {S : Scheme.{u}} {A : Type u}
    [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    {Y : (Over S)ᵒᵖ ⥤ Type u} [IsMcQuillanAffine Y]
    (f : Y ⟶ (spf A hA).obj) [FiniteType f] :
    ∃ r : ℕ, ∃ i : Y ⟶ (affineSpace hA r).obj,
      ClosedImmersion i ∧
        i ≫ (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
            (affineSpace.proj hA r) = f :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
