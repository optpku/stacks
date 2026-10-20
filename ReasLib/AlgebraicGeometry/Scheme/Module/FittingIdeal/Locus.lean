module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Loci defined by Fitting ideal sheaves

This file defines the open complements of Fitting closed subschemes and the
successive locally closed rank loci in the Fitting filtration.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The open complement of the closed subscheme cut out by the `r`th Fitting ideal sheaf. -/
abbrev fittingOpenComplement
    {S : Scheme.{u}} (F : S.Modules) (r : ℕ) : Opens S :=
  ⟨((((fittingIdealSheaf F r).support : Closeds S) : Set S)ᶜ),
    (fittingIdealSheaf F r).support.2.isOpen_compl⟩

/-- The locally closed locus between the preceding and the `r`th Fitting closed subschemes,
with the preceding closed subscheme at rank zero understood to be the ambient scheme. -/
abbrev fittingRankLocus
    {S : Scheme.{u}} (F : S.Modules) : ℕ → Scheme
  | 0 => (fittingOpenComplement F 0).toScheme
  | r + 1 =>
      (((fittingIdealSheaf F r).subschemeι) ⁻¹ᵁ fittingOpenComplement F (r + 1)).toScheme

/-- The canonical morphism from a Fitting rank locus to the ambient scheme. -/
abbrev fittingRankLocusι
    {S : Scheme.{u}} (F : S.Modules) : (r : ℕ) → fittingRankLocus F r ⟶ S
  | 0 => (fittingOpenComplement F 0).ι
  | r + 1 =>
      (((fittingIdealSheaf F r).subschemeι) ⁻¹ᵁ fittingOpenComplement F (r + 1)).ι ≫
        (fittingIdealSheaf F r).subschemeι

end AlgebraicGeometry.Scheme
