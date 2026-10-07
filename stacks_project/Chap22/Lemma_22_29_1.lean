module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory
open DifferentialGradedBimodule

universe u v w x y

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}
variable (N : DifferentialGradedBimodule.{u, w, x, y} A B)

/- Lemma 22.29.1 (09LM): tensoring on the right by a differential graded bimodule is a
differential graded functor; it canonically induces functors on closed degree-zero morphisms and
on homotopy classes. -/
@[stacks 09LM] #check
  (Tensor.dgFunctor N : DgFunctor R (DifferentialGradedModule.{u, v} A)
    (DifferentialGradedModule.{u, max v w} B))
#check ((Tensor.dgFunctor N).mapComp : Comp R (DifferentialGradedModule.{u, v} A) ⥤
  Comp R (DifferentialGradedModule.{u, max v w} B))
#check ((Tensor.dgFunctor N).mapK : K R (DifferentialGradedModule.{u, v} A) ⥤
  K R (DifferentialGradedModule.{u, max v w} B))

/- Passing a mapped closed degree-zero morphism to the homotopy category agrees with mapping its
homotopy class directly. -/
#check DgFunctor.mapK_map_inK (Tensor.dgFunctor N)
