/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy.Limits
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits DifferentialGradedCategory
open scoped DifferentialGradedCategory

universe u v w

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/- Lemma 22.5.4 (1) (09JR): the intrinsic homotopy category of right DG `A`-modules
has arbitrary direct sums. -/
@[stacks 09JR] #check
  (inferInstance : HasCoproducts.{w} (K R (DifferentialGradedModule.{u, w} A)))

/- Lemma 22.5.4 (2) (09JR): the intrinsic homotopy category of right DG `A`-modules
has arbitrary products. -/
@[stacks 09JR] #check
  (inferInstance : HasProducts.{w} (K R (DifferentialGradedModule.{u, w} A)))

#check @DifferentialGradedModule.Homotopy.toKPreservesCoproducts
#check @DifferentialGradedModule.Homotopy.toKPreservesProducts
