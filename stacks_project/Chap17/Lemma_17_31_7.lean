module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.Transitivity
import StacksCheckRecall

@[expose] public section

/-! Lemma 17.31.7 (0E1Z): composable morphisms `X ⟶ Y ⟶ Z` of ringed spaces have a canonical
map from `f^* NL(Y/Z)` to the mapping cocone of `NL(X/Z) ⟶ NL(X/Y)`.  It is an isomorphism on
`H⁰` and an epimorphism on `H⁻¹`, producing the canonical six-term exact sequence. -/
@[stacks 0E1Z]
#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.transitivity

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Transitivity

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.pullbackComplex

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Pullback.chosenComplex

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Pullback.factoredComplex

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Pullback.factorizationIso

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Pullback.factorizationIso_hom_f

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Pullback.factorizationIso_inv_f

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Pullback.comparisonIso

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Pullback.comparisonIso_hom_f
#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Pullback.comparisonIso_hom
#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Pullback.comparisonIso_inv

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Pullback.chosenComplexIso

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Pullback.chosenComplexIso_hom

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Pullback.chosenComplexIso_hom_f

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Pullback.chosenComplexIso_inv_f

#check @SheafOfModules.RingedSite.InverseImage.Factorization.complexObjIso_hom_f

#check @SheafOfModules.RingedSite.InverseImage.Factorization.complexObjIso_inv_f

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.compositionIso

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.left

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.comparison

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.toCocone

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Transitivity.sixTerm

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Transitivity.sixTerm_exact

#check @AlgebraicGeometry.RingedSpace.NaiveCotangent.Transitivity.comparison_zero_epi
