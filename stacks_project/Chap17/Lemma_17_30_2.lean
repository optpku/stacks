module

public import ReasLib.Topology.Sheaves.Algebraic.DeRham.InverseImage
import StacksCheckRecall

@[expose] public section

/- Lemma 17.30.2 (0FKP): inverse image along a continuous map preserves the relative de Rham
complex. -/
@[stacks 0FKP]
#check @TopCat.Sheaf.DeRham.InverseImage.iso

#check @TopCat.Sheaf.DeRham.InverseImage.comparison
#check @TopCat.Sheaf.DeRham.InverseImage.comparisonApp
#check @SheafOfModules.RingedSite.DeRham.comparisonAppInv
#check @SheafOfModules.RingedSite.DeRham.comparisonApp_hom_inv_id
#check @SheafOfModules.RingedSite.DeRham.comparisonApp_inv_hom_id
#check @TopCat.Sheaf.DeRham.InverseImage.comparisonAppIso
#check @TopCat.Sheaf.DeRham.InverseImage.comparisonAppIso_inv
#check @SheafOfModules.RingedSite.DeRham.comparisonAppIso_comm
#check @SheafOfModules.RingedSite.DeRham.comparisonInv
#check @SheafOfModules.RingedSite.DeRham.comparison_hom_inv_id
#check @SheafOfModules.RingedSite.DeRham.comparison_inv_hom_id
#check @SheafOfModules.RingedSite.DeRham.comparison_isIso
#check @SheafOfModules.RingedSite.DeRham.comparisonIso
#check @SheafOfModules.RingedSite.DeRham.comparisonIso_inv
#check @TopCat.Sheaf.DeRham.InverseImage.iso_hom
#check @TopCat.Sheaf.DeRham.InverseImage.iso_inv
#check @TopCat.Sheaf.DeRham.InverseImage.iso_hom_f
#check @TopCat.Sheaf.DeRham.InverseImage.iso_inv_f
#check @TopCat.Sheaf.DeRham.InverseImage.inverseImage_isIsomorphic
