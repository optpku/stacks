/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.Stalk
import StacksCheckRecall

@[expose] public section

open TopCat.Sheaf.NaiveCotangent

/- Lemma 17.31.4 (0D09): the stalk of the naive cotangent complex is the algebraic naive
cotangent complex of the induced morphism on stalk rings. -/
@[stacks 0D09]
#check @stalkIso
#check @stalkIso_hom
#check @stalkIso_inv

/- The forward components and visible differential compatibility of the canonical isomorphism. -/
#check @stalkIso_hom_f_negOne
#check @stalkIso_hom_f_zero
#check @stalkIso_inv_f_negOne
#check @stalkIso_inv_f_zero
#check @stalkIso_hom_d_negOne_zero

/- The two visible terms and differential of the stalkwise complex. -/
#check @stalk_X_negOne
#check @stalk_X_zero
#check @stalk_d_negOne_zero

/- The data-safe conormal-stalk comparisons and their isomorphism properties. -/
#check @TopCat.Sheaf.Conormal.Stalk.algebraicComparison
#check @TopCat.Sheaf.Conormal.Stalk.algebraicComparisonInv
#check @TopCat.Sheaf.Conormal.Stalk.algebraicComparison_isIso
#check @TopCat.Sheaf.Conormal.Stalk.algebraicComparisonIso
#check @TopCat.Sheaf.Conormal.Stalk.algebraicComparisonIso_inv
#check @TopCat.Sheaf.Conormal.Stalk.sheafComparison
#check @TopCat.Sheaf.Conormal.Stalk.sheafComparisonInv
#check @TopCat.Sheaf.Conormal.Stalk.sheafComparison_isIso
#check @TopCat.Sheaf.Conormal.Stalk.sheafComparisonIso
#check @TopCat.Sheaf.Conormal.Stalk.sheafComparisonIso_inv
#check @TopCat.Sheaf.Conormal.Stalk.sheafStalkIso
#check @TopCat.Sheaf.Conormal.Stalk.sheafStalkIso_hom
#check @TopCat.Sheaf.Conormal.Stalk.sheafStalkIso_inv
#check @TopCat.Sheaf.Conormal.Stalk.tensorComparison
#check @TopCat.Sheaf.Conormal.Stalk.tensorComparisonInv
#check @TopCat.Sheaf.Conormal.Stalk.tensorComparison_isIso
#check @TopCat.Sheaf.Conormal.Stalk.tensorComparisonIso
#check @TopCat.Sheaf.Conormal.Stalk.tensorComparisonIso_inv
#check @TopCat.Sheaf.Conormal.Stalk.tensorStalkIso
#check @TopCat.Sheaf.Conormal.Stalk.tensorStalkIso_hom
#check @TopCat.Sheaf.Conormal.Stalk.tensorStalkIso_inv

/- The explicit identifications of the two presentation terms. -/
#check @PresentationStalk.negOneIso
#check @PresentationStalk.negOneIso_hom
#check @PresentationStalk.negOneIso_inv
#check @PresentationStalk.zeroIso
#check @PresentationStalk.zeroIso_hom
#check @PresentationStalk.zeroIso_inv
