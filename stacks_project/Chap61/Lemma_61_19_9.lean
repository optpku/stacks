module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleLocallyConstant
import StacksCheckRecall

/-!
# Lemma 61.19.9

Inverse image `ε⁻¹` along `etaleToProEt` is an equivalence between locally
constant sheaves of finitely presented `Λ`-modules on the small étale and
small pro-étale sites.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type w) [Ring Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{max (u + 1) w} Λ)]
variable [HasWeakSheafify (ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)]
variable [∀ U : X.Etale,
    HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{max (u + 1) w} Λ)]
variable [∀ U : X.ProEt,
    HasWeakSheafify ((ProEt.topology X).over U) (ModuleCat.{max (u + 1) w} Λ)]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{max (u + 1) w} Λ,
    (etaleToProEt X).op.HasLeftKanExtension F]

/- Lemma 61.19.9: for a scheme `X` and a ring `Λ`, inverse image `ε⁻¹` along
`etaleToProEt` is an equivalence between locally constant sheaves of finitely
presented `Λ`-modules on `X.Etale` and the same class on `X.ProEt`. -/
@[stacks 099Y]
#check (AlgebraicGeometry.Scheme.etaleToProEtPullback_locallyConstantFP_isEquivalence X Λ :
    (AlgebraicGeometry.Scheme.etaleToProEtPullback_locallyConstantFP X Λ).IsEquivalence)

end AlgebraicGeometry.Scheme
