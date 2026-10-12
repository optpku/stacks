/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Spectral.Limit.Basic

/-!
# Spectral inverse limits

This module supplies spectrality of a cofiltered spectral limit and spectrality of its projection
maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

noncomputable section

variable {I : Type v} [Category.{w} I] [IsCofiltered I]

/-- The point of a limiting cone over a cofiltered spectral diagram is a spectral space. -/
@[stacks 0A2Z "spectral inverse limits"]
theorem spectralSpace_of_isLimit_of_cofiltered_spectral_diagram
    {F : I ⥤ TopCat.{max u v}} [∀ i, SpectralSpace (F.obj i)] {C : Cone F}
    (hC : IsLimit C)
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a)) :
    SpectralSpace C.pt := sorry

/-- Every projection from a limiting cone over a cofiltered spectral diagram is a spectral map. -/
@[stacks 0A2Z "spectral inverse-limit projections"]
theorem isSpectralMap_projection_of_isLimit_of_cofiltered_spectral_diagram
    {F : I ⥤ TopCat.{max u v}} [∀ i, SpectralSpace (F.obj i)] {C : Cone F}
    (hC : IsLimit C)
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (i : I) :
    IsSpectralMap (C.π.app i) := sorry

namespace TopCat

/-- A cofiltered limit of spectral spaces with spectral transition maps is
spectral.  This is the chosen-limit specialization of the limiting-cone API. -/
theorem spectralSpace_limit_of_cofiltered_spectralDiagram
    {F : I ⥤ TopCat.{max u v}} [∀ i, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a)) :
    SpectralSpace (limit F : TopCat) := sorry

/-- The canonical projection from a cofiltered spectral limit is a spectral
map. -/
theorem isSpectralMap_limit_π_of_cofiltered_spectralDiagram
    {F : I ⥤ TopCat.{max u v}} [∀ i, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (i : I) :
    IsSpectralMap (limit.π F i) := sorry

end TopCat
