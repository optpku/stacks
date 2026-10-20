module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DifferentialGradedCategory
open DifferentialGradedBimodule

noncomputable section

universe u v w x y

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}
variable (N : DifferentialGradedBimodule.{u, w, x, y} A B)
variable (M : Comp R (DifferentialGradedModule.{u, v} A))
variable {M' : Comp R (DifferentialGradedModule.{u, v} A)} (f : M ⟶ M')

/- Equation 22.33.0.1 (09LQ): tensoring by a differential graded `(A, B)`-bimodule induces
the displayed functor from right DG `A`-modules to right DG `B`-modules. -/
@[stacks 09LQ] #check
  ((Tensor.dgFunctor N).mapComp : Comp R (DifferentialGradedModule.{u, v} A) ⥤
    Comp R (DifferentialGradedModule.{u, max v w} B))

#check Tensor.dgFunctor_obj N M
#check (Tensor.dgFunctor N).mapComp.map f
