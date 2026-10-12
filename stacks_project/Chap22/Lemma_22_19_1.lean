/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {I M : DifferentialGradedModule.{u, w} A} (f : I ⟶ M)
variable [Mono ((forgetToGraded A).map f)] [Injective I.toGraded]

/- Lemma 22.19.1 (09K2): a DG-module morphism is admissibly monic when its underlying
graded `A`-module morphism is monic and its underlying source is injective. -/
@[stacks 09K2] #check
  (isAdmissibleMono_of_mono_of_injective f : IsAdmissibleMono f)
