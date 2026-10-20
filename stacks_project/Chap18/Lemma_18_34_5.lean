module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.Sheafification
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.PrincipalParts.Sheafification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}}
variable (phi : O₁ ⟶ O₂)
variable (F : PresheafOfModules (ringPresheaf O₂)) (k : ℕ)

/- Lemma 18.34.5 (09CV): principal parts after sheafifying `O₁`, `O₂`, and `F` are
canonically the sheaf associated to the presheaf
`X ↦ PrincipalParts.RingHom.module (phi.app X).hom (F.obj X) k`. -/
@[stacks 09CV]
#check (comparisonIso J phi F k :
  ofPresheaf J phi F k ≅ afterSheafification J phi F k)

#check @comparison
#check @comparison_isIso
#check @comparisonIso_hom
#check @comparisonIso_hom_adj
#check @comparisonNatIso
#check @comparisonNatIso_hom_app

end SheafOfModules.RingedSite.PrincipalParts.Sheafification
