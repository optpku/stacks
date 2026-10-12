/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.DerivedMorita.Tensor
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (N : DifferentialGradedBimodule A B)
variable (h_compact : IsCompactObject N.rightDerivedObject)
variable (h_selfExt : N.HasSelfExtComparison)
variable (h_classical : CategoryTheory.IsClassicalGeneratorOfCompacts N.rightDerivedObject)

/- Remark 22.37.3 (09SS): the zero-detection hypothesis may be replaced by classical generation
of the compact subcategory. -/
@[stacks 09SS] #check
  (CochainDGAlgebra.DerivedMorita.Tensor.isEquivalence_of_classicalGenerator
      N h_compact h_classical h_selfExt :
    (DifferentialGradedBimodule.Tensor.derivedFunctor N).IsEquivalence)

variable (h_rHom_regular : IsCompactObject
  ((DifferentialGradedBimodule.InternalHom.derivedFunctor N).obj
    (DifferentialGradedModule.Derived.regularObject B)))
variable (h_generator : CategoryTheory.IsWeakGeneratorOfCompacts N.rightDerivedObject)

/- If the derived Hom from the bimodule to the regular object is compact, weak generation of the
compact subcategory suffices. -/
#check
  (CochainDGAlgebra.DerivedMorita.Tensor.isEquivalence_of_weakCompactGenerator
      N h_compact h_rHom_regular h_generator h_selfExt :
    (DifferentialGradedBimodule.Tensor.derivedFunctor N).IsEquivalence)

#check @CategoryTheory.IsClassicalGeneratorOfCompacts
#check @CategoryTheory.IsWeakGeneratorOfCompacts
#check @CategoryTheory.isClassicalGeneratorOfCompacts_iff
#check @CategoryTheory.isWeakGeneratorOfCompacts_iff
#check @CategoryTheory.IsCompactObject.isWeakGenerator
