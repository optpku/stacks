module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.OpenComplement.Discrete

/-!
# Picard extension across a discrete open complement

This leaf applies the reusable open-complement conditions to invertible scheme
modules and Picard pullback.  The nonvanishing open is the existing canonical
`Modules.Invertible.sectionNonvanishingOpen`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OpenComplement

variable {X : Scheme.{u}}

/-- A retrocompact open with discrete, Noetherian, at-most-one-dimensional
complement is the nonvanishing open of a section of an invertible scheme
module. -/
@[stacks 09NA]
theorem exists_invertibleModule_sectionNonvanishingOpen
    (U : X.Opens) [QuasiCompact U.ι]
    (h_discrete : IsDiscrete ((U : Set X)ᶜ)) [StalksNoetherianDimLEOne U] :
    ∃ (L : X.Modules) (hL : Modules.Invertible L) (s : Γ(L, ⊤)),
      U = hL.sectionNonvanishingOpen s := sorry

section

variable (U : X.Opens)

/-- Restriction to a retrocompact open with discrete, Noetherian,
at-most-one-dimensional complement is surjective on Picard groups. -/
@[stacks 09NA]
theorem picardPullback_surjective
    [QuasiCompact U.ι] (h_discrete : IsDiscrete ((U : Set X)ᶜ))
    [StalksNoetherianDimLEOne U] :
    Function.Surjective (Scheme.Hom.picardPullback U.ι) := sorry

end

end AlgebraicGeometry.Scheme.OpenComplement
