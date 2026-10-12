/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.InverseImage
import StacksCheckRecall

@[expose] public section

/-! Lemma 17.28.6 (08RR): inverse image along a continuous map commutes canonically with
relative differentials, compatibly with the universal derivation. -/
@[stacks 08RR]
#check @TopCat.Sheaf.RelativeDifferentials.InverseImage.iso
#check @TopCat.Sheaf.RelativeDifferentials.InverseImage.iso_hom
#check @TopCat.Sheaf.RelativeDifferentials.InverseImage.iso_inv

#check @TopCat.Sheaf.RelativeDifferentials.InverseImage.comparison
#check @TopCat.Sheaf.RelativeDifferentials.InverseImage.comparisonInv
#check @TopCat.Sheaf.RelativeDifferentials.InverseImage.comparison_hom_inv_id
#check @TopCat.Sheaf.RelativeDifferentials.InverseImage.comparison_inv_hom_id

#check @TopCat.Sheaf.RelativeDifferentials.InverseImage.comparison_spec

#check @TopCat.Sheaf.RelativeDifferentials.InverseImage.eq_comparison

#check @SheafOfModules.RingedSite.RelativeDifferentials.comparison_spec
#check @SheafOfModules.RingedSite.RelativeDifferentials.eq_comparison
