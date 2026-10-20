/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.TwistGluing

/-!
# Flatness of relative projective spectra

This file records flatness consequences of eventual flatness of the nonnegative degree pieces
of a graded algebra presented by a relative projective spectrum with its canonical twists.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation

variable {S X : Scheme.{u}} {p : X ⟶ S}
variable {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf} [𝒜.IsCommutative]
variable {A σ : S.affineOpens → Type u}
variable [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
variable [∀ U, AddSubgroupClass (σ U) (A U)]
variable {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
variable [∀ U, GradedRing (sectionGrading U)]
variable {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}

/-- The nonnegative degree pieces of the graded algebra in a relative-projective twist
presentation are eventually flat when they are flat in all sufficiently large degrees. -/
def EventuallyFlatDegreePieces
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d}
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p) : Prop :=
  ∀ᶠ d : ℕ in Filter.atTop, (𝒜 (Int.ofNat d)).IsFlat

/-- Eventual flatness of the nonnegative degree pieces of a relative projective-spectrum
presentation implies flatness of its structural morphism. -/
theorem flat_of_eventuallyFlatDegreePieces
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}
    (hqc : 𝒜.IsQuasicoherent)
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U))
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) p)
    (hflat : presentation.EventuallyFlatDegreePieces) :
    AlgebraicGeometry.Flat p := sorry

/-- Eventual flatness of the nonnegative degree pieces of a relative projective-spectrum
presentation makes every integral twist flat over the base. -/
theorem twist_flatOver_of_eventuallyFlatDegreePieces
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}
    (hqc : 𝒜.IsQuasicoherent)
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U))
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) p)
    (hflat : presentation.EventuallyFlatDegreePieces) (d : ℤ) :
    AlgebraicGeometry.Scheme.Modules.flatOver (presentation.twistAlgebra d) p := sorry

/-- Eventual flatness of the nonnegative degree pieces of a relative projective-spectrum
presentation makes its structural morphism and every integral twist flat over the base. -/
theorem flat_and_twist_flatOver_of_eventuallyFlatDegreePieces
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}
    (hqc : 𝒜.IsQuasicoherent)
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U))
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) p)
    (hflat : presentation.EventuallyFlatDegreePieces) :
    AlgebraicGeometry.Flat p ∧
      ∀ d : ℤ, AlgebraicGeometry.Scheme.Modules.flatOver
        (presentation.twistAlgebra d) p := sorry

end AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation
