module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.InternalHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.PullbackInternalHom

/- Lemma 17.22.5 (0C6I): the canonical pullback--internal-Hom comparison is invertible for a
flat morphism and a finitely presented source. -/
@[stacks 0C6I]
#check @isIso_of_isFlat

/- The pullback--internal-Hom comparison is exposed as morphism, Iso, and natural Iso data. -/
#check @comparison
#check @comparison_naturality
#check @comparison_naturality_left
#check @natTrans
#check @natTrans_app
#check @comparison_isIso_of_isFlat
#check @comparisonInv
#check @comparison_comp_comparisonInv
#check @comparisonInv_comp_comparison
#check @comparisonIso
#check @comparisonIso_hom
#check @comparisonIso_inv
#check @comparisonInv_naturality
#check @natTransInv
#check @natTransInv_app
#check @natTrans_comp_natTransInv
#check @natTransInv_comp_natTrans
#check @natTrans_isIso
#check @comparisonNatIso
#check @comparisonNatIso_hom
#check @comparisonNatIso_inv
#check @comparisonNatIso_app
#check @comparisonNatIso_hom_app
#check @comparisonNatIso_inv_app

end AlgebraicGeometry.RingedSpace.Hom.PullbackInternalHom
