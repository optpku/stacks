/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Ideal.Regularity.ProjectiveDimension

@[expose] public section

/-!
# Regular-Ideal Projective-Dimension Criterion Recall

The source criterion is owned by the regular-ideal API.  Its explicit
finite-local-freeness form and its instance-driven companion are both
available from the narrow ReasLib leaf.
-/

/- Proposition 23.11.3, tag 0FJS: if `I` has finite projective dimension as
an `R`-module and `I.Cotangent` is finite locally free over `R ⧸ I`, then
`I.IsRegularIdeal`. -/
universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {I : Ideal R}
variable (hpd : CategoryTheory.projectiveDimension (ModuleCat.of R I) ≠ ⊤)
variable (hcot : Module.FiniteLocallyFree (R ⧸ I) I.Cotangent)

@[stacks 0FJS "regular ideal criterion from projective dimension"]
#check (Ideal.IsRegularIdeal.of_finiteProjectiveDimension hpd hcot : I.IsRegularIdeal)

end

#check @Ideal.IsRegularIdeal.of_finiteProjectiveDimension_of_finiteLocallyFree
