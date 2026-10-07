module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.OpenComplement

@[expose] public section

/-!
# Lemma 33.38.3 canonical checks

Both conclusions are owned by the scheme open-complement Picard API.
-/

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.38.3 (1): a retrocompact open with discrete, Noetherian,
at-most-one-dimensional complement is the nonvanishing open of a section of
an invertible scheme module. -/
@[stacks 09NA] #check
  (AlgebraicGeometry.Scheme.OpenComplement.exists_invertibleModule_sectionNonvanishingOpen :
    ∀ {X : Scheme.{u}} (U : X.Opens) [QuasiCompact U.ι]
      (_ : IsDiscrete ((U : Set X)ᶜ))
      [Scheme.OpenComplement.StalksNoetherianDimLEOne U],
      ∃ (L : X.Modules) (hL : Scheme.Modules.Invertible L) (s : Γ(L, ⊤)),
        U = hL.sectionNonvanishingOpen s)

/- Lemma 33.38.3 (2): restriction to a retrocompact open with discrete,
Noetherian, at-most-one-dimensional complement is surjective on Picard
groups. -/
@[stacks 09NA] #check
  (AlgebraicGeometry.Scheme.OpenComplement.picardPullback_surjective :
    ∀ {X : Scheme.{u}} (U : X.Opens) [QuasiCompact U.ι]
      (_ : IsDiscrete ((U : Set X)ᶜ))
      [Scheme.OpenComplement.StalksNoetherianDimLEOne U],
      Function.Surjective (Scheme.Hom.picardPullback U.ι))
