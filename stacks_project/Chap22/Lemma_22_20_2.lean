/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.KProjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

universe u v

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {P N : DifferentialGradedModule.{u, v} A}
variable (hP : DifferentialGradedModule.HasPropertyP A P)
variable (hN : DifferentialGradedModule.Homotopy.acyclic A
  ((DifferentialGradedModule.toK A).obj N))
variable (f : (DifferentialGradedModule.toK A).obj P ⟶
  (DifferentialGradedModule.toK A).obj N)

/- Lemma 22.20.2 (09KM): every morphism from a property P right DG module to an acyclic right DG
module is zero in the intrinsic homotopy category. -/
@[stacks 09KM] #check
  (DifferentialGradedModule.HasPropertyP.hom_eq_zero_of_acyclic hP hN f : f = 0)
