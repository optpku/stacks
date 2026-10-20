module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flatness.LocallyFree
public import ReasLib.RingTheory.Ideal.Cotangent.ProjectiveDimension
public import ReasLib.RingTheory.Ideal.Regularity

@[expose] public section

/-!
# Regular Ideals from Projective Dimension

This leaf records the criterion that finite projective dimension together with
finite local freeness of an ideal's conormal module implies local regularity of
the ideal.
-/

open CategoryTheory

universe u

namespace Ideal.IsRegularIdeal

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {I : Ideal R}

/-- Proposition 23.11.3, tag `0FJS`: an ideal of finite projective dimension
whose cotangent module is finite locally free over the quotient is regular. -/
@[stacks 0FJS "regular ideal criterion from projective dimension"]
theorem of_finiteProjectiveDimension
    (hpd : projectiveDimension (ModuleCat.of R I) ≠ ⊤)
    (hcot : Module.FiniteLocallyFree (R ⧸ I) I.Cotangent) :
    I.IsRegularIdeal := sorry

/-- The regular-ideal criterion with finite local freeness supplied by typeclass inference. -/
theorem of_finiteProjectiveDimension_of_finiteLocallyFree
    (hpd : projectiveDimension (ModuleCat.of R I) ≠ ⊤)
    [Module.FiniteLocallyFree (R ⧸ I) I.Cotangent] :
    I.IsRegularIdeal := sorry

end Ideal.IsRegularIdeal
