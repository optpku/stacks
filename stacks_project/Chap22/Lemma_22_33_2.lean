module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory
open DifferentialGradedBimodule

universe u v w x y

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}
variable (N : DifferentialGradedBimodule.{u, w, x, y} A B)

/- Lemma 22.33.2 (09LS): tensoring with a DG bimodule has a canonical total left-derived
functor `- ⊗ᴸ_A N`, constructed from property-(P) resolutions. -/
@[stacks 09LS]
#check
  (Tensor.derivedFunctor.{u, v, w, x, y} N :
    DifferentialGradedModule.Derived.Category.{u, v} A ⥤
      DifferentialGradedModule.Derived.Category.{u, max v w} B)

#check @Tensor.hasDerivedFunctor
#check @Tensor.derivedCounit
#check @Tensor.derivedFunctor_isLeftDerived
