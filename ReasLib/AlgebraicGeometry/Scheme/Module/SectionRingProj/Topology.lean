module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Localization.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Module.SectionRingProj

/-!
# Topology of morphisms to projective spectra of section rings

The canonical basic-open description of a morphism to the projective spectrum of an invertible
module's section ring implies quasi-compactness and dominance on a quasi-compact scheme.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

namespace GradedSections

/-- A positive-degree homogeneous section whose nonvanishing open is empty is nilpotent in the
section ring. -/
theorem isNilpotent_of_nonvanishingOpen_eq_bot [CompactSpace X]
    {L : X.Modules} [hL : Invertible L] {n : ℕ} (hn : 0 < n)
    (s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤))
    (hs : hL.nonvanishingOpen s = ⊥) :
    IsNilpotent (DirectSum.InternalGrading.summandEquiv
      (RingedSpace.GradedSections.degree L) n s :
        RingedSpace.GradedSections.ring L) := sorry

end GradedSections

namespace IsSectionRingProjMap

variable {L : X.Modules} [Invertible L]
variable {f : X ⟶ Proj (RingedSpace.GradedSections.grading L)}

/-- A section-ring projective morphism from a quasi-compact scheme is quasi-compact. -/
theorem quasiCompact [CompactSpace X] (hf : IsSectionRingProjMap L f) :
    QuasiCompact f := sorry

/-- A section-ring projective morphism from a quasi-compact scheme has dense image. -/
theorem isDominant [CompactSpace X] (hf : IsSectionRingProjMap L f) :
    IsDominant f := sorry

/-- A section-ring projective morphism from a quasi-compact scheme is quasi-compact and has
dense image. -/
theorem quasiCompact_and_isDominant [CompactSpace X]
    (hf : IsSectionRingProjMap L f) : QuasiCompact f ∧ IsDominant f := sorry

end IsSectionRingProjMap

end AlgebraicGeometry.Scheme.Modules
