/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
import StacksCheckRecall

@[expose] public section

/-!
# Global Hom-complex cohomology

The displayed equation is the canonical Hom-complex cohomology equivalence specialized to the
category of modules on a ringed site. No chapter-specific alias or proof is needed.
-/

open CategoryTheory
open CochainComplex.HomComplex
open CochainComplex.HomComplex.CohomologyClass

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (O : Sheaf J CommRingCat.{max u v})
variable (L M : CochainComplex (ringedSiteModuleCategory J O) ℤ) (n : ℤ)

/- 21.34.0.2 (0A8Z): degree-`n` global Hom-complex cohomology is the morphism group into the
`n`-shifted target in the homotopy category. -/
@[stacks 0A8Z "global Hom-complex cohomology"]
#check (homologyAddEquiv L M n).trans homAddEquiv

end SheafOfModules.RingedSite
