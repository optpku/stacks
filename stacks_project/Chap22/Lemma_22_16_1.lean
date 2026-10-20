/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible
import StacksCheckRecall

@[expose] public section

universe u v w

open CategoryTheory
open scoped DifferentialGradedModule

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {M P : DifferentialGradedModule.{u, w} A} (f : M ⟶ P)
variable [Epi ((forgetToGraded A).map f)] [Projective P.toGraded]

/- Lemma 22.16.1 (09K0): an epimorphism of DG `A`-modules whose target is projective as a
graded `A`-module is admissibly epic. -/
@[stacks 09K0] #check
  (isAdmissibleEpi_of_epi_of_projective f : IsAdmissibleEpi f)

#check @isAdmissibleEpi_iff_exists_section

end DifferentialGradedModule
