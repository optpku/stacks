/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Stalk
import StacksCheckRecall

@[expose] public section

/- Lemma 17.28.7 (08TE): the stalk of the sheaf of relative differentials is canonically
isomorphic to the module of differentials of the induced morphism on stalk rings. -/
@[stacks 08TE]
#check @TopCat.Sheaf.RelativeDifferentials.Stalk.iso
#check @TopCat.Sheaf.RelativeDifferentials.Stalk.iso_hom
#check @TopCat.Sheaf.RelativeDifferentials.Stalk.iso_inv

#check @TopCat.Sheaf.RelativeDifferentials.Stalk.comparison
#check @TopCat.Sheaf.RelativeDifferentials.Stalk.comparisonInv
#check @TopCat.Sheaf.RelativeDifferentials.Stalk.comparison_d
#check @TopCat.Sheaf.RelativeDifferentials.Stalk.comparisonInv_d
#check @TopCat.Sheaf.RelativeDifferentials.Stalk.iso_hom_d
#check @TopCat.Sheaf.RelativeDifferentials.Stalk.comparison_germ_d
#check @TopCat.Sheaf.RelativeDifferentials.Stalk.comparisonInv_d_germ
#check @TopCat.Sheaf.RelativeDifferentials.Stalk.iso_hom_germ_d
