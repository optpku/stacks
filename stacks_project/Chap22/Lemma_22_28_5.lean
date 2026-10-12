/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.PropertyP
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.Telescope
import StacksCheckRecall

@[expose] public section

universe u v w

open DifferentialGradedBimodule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R} {B : CochainDGAlgebra.{u, w} R}
variable {P : DifferentialGradedBimodule.{u, max v w, v, w} A B}
variable (F : PropertyP.Filtration A B P)

/- Lemma 22.28.5 (0FQL): the telescope sequence of a property P DG bimodule filtration is
admissibly short exact, hence split exact after forgetting to graded bimodules. -/
@[stacks 0FQL] #check
  (DifferentialGradedModule.PropertyP.Filtration.telescopeIsAdmissibleShortExact F :
    DifferentialGradedModule.IsAdmissibleShortExact
      (DifferentialGradedModule.PropertyP.Filtration.telescopeShortComplex F))
