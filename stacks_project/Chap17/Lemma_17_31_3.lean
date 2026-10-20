module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.InverseImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.NaiveCotangent.InverseImage

variable {X Y : TopCat.{u}} {O₁ O₂ : X.Sheaf CommRingCat.{u}}
variable (f : Y ⟶ X) (φ : O₁ ⟶ O₂)

/- Lemma 17.31.3 (08TM): inverse image preserves the naive cotangent complex. -/
@[stacks 08TM]
#check comparisonIso f φ

#check @comparison
#check @comparison_isIso
#check @comparisonInv
#check @comparison_hom_inv_id
#check @comparison_inv_hom_id
#check @source
#check @target
#check @comparisonIso_hom
#check @comparisonIso_hom_f
#check @comparisonIso_inv
#check @comparisonIso_inv_f
#check @comparisonIso_hom_f_negOne
#check @comparisonIso_hom_f_zero
#check @comparisonIso_inv_f_negOne
#check @comparisonIso_inv_f_zero
#check @comparison_f
#check @comparison_f_negOne
#check @comparison_f_zero

#check @SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Comparison.appInv
#check @SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Comparison.app_hom_inv_id
#check @SheafOfModules.RingedSite.NaiveCotangent.InverseImage.Comparison.app_inv_hom_id

#check @SheafOfModules.RingedSite.Conormal.InverseImage.pullbackComparisonIso
#check @SheafOfModules.RingedSite.Conormal.InverseImage.pullbackComparisonIso_hom
#check @SheafOfModules.RingedSite.Conormal.InverseImage.pullbackComparisonIso_inv
#check @SheafOfModules.RingedSite.Conormal.InverseImage.pullbackComparison_isIso
#check @SheafOfModules.RingedSite.Conormal.InverseImage.pullbackComparisonInv
#check @SheafOfModules.RingedSite.Conormal.InverseImage.pullbackComparison_hom_inv_id
#check @SheafOfModules.RingedSite.Conormal.InverseImage.pullbackComparison_inv_hom_id

end TopCat.Sheaf.NaiveCotangent.InverseImage
