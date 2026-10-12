/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.Sheafification
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules.RingedSite.PrincipalParts.Sheafification

variable (X : TopCat.{u})
variable {O₁ O₂ : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}}
variable (phi : O₁ ⟶ O₂)
variable (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ)

/- Lemma 17.29.5 (0G3U): sheafifying sectionwise principal parts agrees with taking principal
parts after sheafifying the two ring presheaves and the module presheaf. -/
@[stacks 0G3U]
#check (comparisonIso (Opens.grothendieckTopology X) phi F k :
  ofPresheaf (Opens.grothendieckTopology X) phi F k ≅
    afterSheafification (Opens.grothendieckTopology X) phi F k)

#check @comparison
#check @sourceOperatorHom
#check @sourceOperator
#check @sourceOperator_toHom
#check @comparisonInv
#check @comparisonInv_desc
#check @sourceOperatorHom_comparison
#check @universalOperator_comparisonInv
#check @comparison_comp_comparisonInv
#check @comparisonInv_comp_comparison
#check @comparison_isIso
#check @comparisonIso_hom
#check @comparisonIso_inv
#check @inv_comparison
#check @comparisonIso_hom_adj
#check @comparisonNatIso
#check @comparisonNatTrans_app
#check @invNatTrans_app
#check @comparisonNatTrans_hom_inv_id
#check @comparisonNatTrans_inv_hom_id
#check @invNatTrans
#check @comparisonNatIso_app
#check @comparisonNatIso_hom_app
#check @comparisonNatIso_inv
#check @comparisonNatIso_inv_app

end SheafOfModules.RingedSite.PrincipalParts.Sheafification
