module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.AffineBase
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Vanishing

/-!
# Higher direct images in relative dimension one

This module records vanishing results for higher direct images and global cohomology of
quasicoherent modules along proper morphisms whose fibers have dimension at most one.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HigherDirectImage

variable {X Y : Scheme.{u}}

/-- For a proper morphism whose fibers have dimension at most one and whose fiber structure
sheaves have vanishing first cohomology, all quasicoherent higher direct images above degree
one vanish. -/
theorem vanishesAbove_one_of_fiberH1
    (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
    (hH1 : ∀ y : Y,
      IsZero (Scheme.Modules.cohomology
        (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1)) :
    VanishesAbove f 1 := sorry

/-- If the target of a proper morphism is affine, its fibers have dimension at most one, and
their structure sheaves have vanishing first cohomology, then every quasicoherent module on
the source has vanishing cohomology above degree one. -/
theorem globalCohomology_isZero_above_one_of_affine
    (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
    (hH1 : ∀ y : Y,
      IsZero (Scheme.Modules.cohomology
        (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1))
    [IsAffine Y] (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (p : ℕ) (hp : 1 < p) :
    IsZero (Scheme.Modules.cohomology ℱ p) := sorry

/-- If the target of a proper morphism is affine, its fibers have dimension at most one, and
their structure sheaves have vanishing first cohomology, then a globally generated
quasicoherent module on the source has vanishing first cohomology. -/
theorem globalCohomology_degreeOne_isZero_of_globallyGenerated
    (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
    (hH1 : ∀ y : Y,
      IsZero (Scheme.Modules.cohomology
        (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1))
    [IsAffine Y] (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    [SheafOfModules.IsGloballyGenerated ℱ] :
    IsZero (Scheme.Modules.cohomology ℱ 1) := sorry

/-- For a proper morphism whose fibers have dimension at most one and whose fiber structure
sheaves have vanishing first cohomology, the degree-one higher direct image of a
quasicoherent quotient of a pulled-back quasicoherent module vanishes. -/
theorem degreeOne_isZero_of_epi_pullback
    (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
    (hH1 : ∀ y : Y,
      IsZero (Scheme.Modules.cohomology
        (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (𝒢 : Y.Modules) [𝒢.IsQuasicoherent]
    (π : (Scheme.Modules.pullback f).obj 𝒢 ⟶ ℱ) [Epi π] :
    IsZero (RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ 1) := sorry

end AlgebraicGeometry.Scheme.HigherDirectImage
