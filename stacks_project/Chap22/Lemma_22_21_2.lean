/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI.KInjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory DifferentialGradedModule
open scoped DifferentialGradedCategory

universe u v

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {N I : DifferentialGradedModule.{u, v} A}
variable (hI : DifferentialGradedModule.HasPropertyI A I)
variable (hN : DifferentialGradedModule.Homotopy.acyclic A ((toK A).obj N))
variable (f : (toK A).obj N ⟶ (toK A).obj I)

/- Lemma 22.21.2 (09KS): if `N` is acyclic and `I` has property `(I)`, then every morphism
`N ⟶ I` is zero in the homotopy category of right DG `A`-modules. -/
@[stacks 09KS] #check
  (DifferentialGradedModule.HasPropertyI.hom_eq_zero_of_acyclic hI hN f : f = 0)
