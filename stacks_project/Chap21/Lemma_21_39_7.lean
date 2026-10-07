module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Evaluation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-! Lemma 21.39.7 (08Q9) identifies derived lower shriek with cosimplicial evaluation in both
abelian-group and module-valued forms. The reusable statements are owned by
`CategoryTheory.DerivedColimit`. -/

@[stacks 08Q9 "canonical cosimplicial evaluation augmentation"]
#check @CategoryTheory.CosimplicialObject.Evaluation.colimitAugmentation

@[stacks 08Q9 "derived cosimplicial evaluation augmentation"]
#check @CategoryTheory.CosimplicialObject.Evaluation.derivedAugmentation

@[stacks 08Q9 "abelian and module derived lower-shriek evaluation"]
#check @CategoryTheory.DerivedColimit.single_isomorphic_to_evaluation_abelian

@[stacks 08Q9 "abelian and module derived lower-shriek evaluation"]
#check @CategoryTheory.DerivedColimit.single_isomorphic_to_evaluation_module
