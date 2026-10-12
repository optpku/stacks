/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ExteriorAlgebra.FilteredColimits
public import ReasLib.Algebra.Category.ModuleCat.SymmetricAlgebra.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.TensorAlgebra.Adjunction
import StacksCheckRecall

/-!
# Tensor, symmetric, and exterior algebras of directed colimits

@stack 00DQ
-/

@[expose] public section

@[stacks 00DQ "(1), canonical tensor-algebra functor"]
#check @AlgCat.tensorAlgebra

@[stacks 00DQ "(1), tensor-algebra adjunction"]
#check @AlgCat.tensorAlgebra.adj

@[stacks 00DQ "(2), symmetric-algebra functor"]
#check @CommAlgCat.symmetricAlgebra

@[stacks 00DQ "(2), symmetric-algebra adjunction"]
#check @CommAlgCat.symmetricAlgebra.adj

@[stacks 00DQ "(3), exterior-algebra functor"]
#check @AlgCat.exteriorAlgebra

@[stacks 00DQ "(3), filtered colimits"]
#check @AlgCat.exteriorAlgebra.preservesFilteredColimitsOfSize

@[stacks 00DQ "(3), directed colimits"]
#check @AlgCat.exteriorAlgebra.preservesDirectedColimits

universe u v

open CategoryTheory Limits

section

variable (R : Type u) [CommRing R]
variable (I : Type v) [Preorder I] [IsDirectedOrder I]

@[stacks 00DQ "(1), tensor-algebra preservation inference"]
#check (inferInstance :
  PreservesColimitsOfShape I (AlgCat.tensorAlgebra.{max u v} R))

@[stacks 00DQ "(2), symmetric-algebra preservation inference"]
#check (inferInstance : PreservesColimitsOfShape I
  (CommAlgCat.symmetricAlgebra.{u, max u v} R))

@[stacks 00DQ "(3), exterior-algebra preservation inference"]
#check (inferInstance : PreservesColimitsOfShape I
  (AlgCat.exteriorAlgebra.{u, max u v} R))

end
