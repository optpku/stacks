module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Comparison
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Sites.BoundedCohomologyBasis
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Lower-truncation completeness from bounded cohomology bases

This leaf gives the site-independent interface for the bounded-basis completeness criterion.  A
ringed-site statement is obtained by specializing the sheaf of rings `𝒪` to a structure sheaf.
-/

open CategoryTheory CategoryTheory.GrothendieckTopology

noncomputable section

universe wι w z v u

namespace CategoryTheory.DerivedCategory.CohomologyIn

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max z v}]
variable [HasExt.{max z v} (Sheaf J AddCommGrpCat.{max z v})]
variable (𝒪 : Sheaf J RingCat.{w})
variable (A : ObjectProperty (SheafOfModules.{max z v} 𝒪))
variable [Abelian (SheafOfModules.{max z v} 𝒪)]
variable [CategoryTheory.ObjectProperty.IsWeakSerreClass A]
variable [HasDerivedCategory (SheafOfModules.{max z v} 𝒪)]

/-- Lemma 21.25.2 (0D6S): a bounded cohomology basis forces every compatible lower-truncation
derived-limit comparison from an `A`-cohomological object to be an isomorphism. -/
@[stacks 0D6S]
theorem isIso_of_boundedBasis
    (basis : BoundedCohomologyBasis 𝒪 A)
    (E : CategoryTheory.DerivedCategory.CohomologyIn A)
    (K : DerivedCategory (SheafOfModules.{max z v} 𝒪))
    (c : E.obj ⟶ K)
    (hc : CategoryTheory.DerivedCategory.Truncation.Lower.Comparison.Exists E.obj c) :
    IsIso c := sorry

end CategoryTheory.DerivedCategory.CohomologyIn

end
