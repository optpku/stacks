module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Hom-complex cohomology after localization

The displayed equation is the direct composite of the canonical Hom-complex cohomology-class
equivalence and the homotopy-category realization.  No chapter-specific alias is needed.
-/

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
open CochainComplex.HomComplex.CohomologyClass
open RingedSite.Hom

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {X : _root_.RingedSite.{u, v, w}} {U : X} [HasBinaryProducts X.carrier]
variable (L M : CochainComplex (_root_.RingedSite.ModuleCat X) ℤ) (n : ℤ)

/- 21.34.0.1 (0A8Y): after restriction to `X.localization U`, degree-`n` Hom-complex
cohomology is the morphism group into the shifted target in the homotopy category. -/
@[stacks 0A8Y "localized Hom-complex cohomology"]
#check
  (homologyAddEquiv
      ((localizedRestrictionComplex X U).obj L)
      ((localizedRestrictionComplex X U).obj M) n).trans
    homAddEquiv

end SheafOfModules.RingedSite
