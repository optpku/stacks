module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ExtensionByZero

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- Restriction along an étale morphism commutes with the étale-to-pro-étale
comparison of small sites. -/
theorem etaleRestriction_comp_etaleToProEt :
    etaleRestriction j ⋙ etaleToProEt X =
      etaleToProEt U ⋙ ProEt.restriction j :=
  sorry

section

variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
variable [∀ F : U.ProEtᵒᵖ ⥤ AddCommGrpCat.{w},
  (ProEt.restriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{w}]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
  (etaleToProEt U).op.HasLeftKanExtension F]
variable [HasWeakSheafify (ProEt.topology U) AddCommGrpCat.{w}]
variable [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
  (etaleToProEt X).op.HasLeftKanExtension F]

/-- Étale abelian extension by zero commutes with inverse image along
`etaleToProEt` as functors on abelian sheaves. -/
theorem abelianExtensionByZero_etaleProetale_functor :
    IsIsomorphic
      (abelianExtensionByZero j ⋙ etaleToProEtPullback X AddCommGrpCat.{w})
      (etaleToProEtPullback U AddCommGrpCat.{w} ⋙
        ProEt.abelianExtensionByZero j) :=
  sorry

/-- For an étale morphism `j : U ⟶ X` and an abelian sheaf `G` on the small
étale site of `U`, extension by zero and inverse image along `etaleToProEt`
commute up to isomorphism on the small pro-étale site of `X`. -/
theorem abelianExtensionByZero_etaleProetale
    (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{w}) :
    IsIsomorphic
      ((etaleToProEtPullback X AddCommGrpCat.{w}).obj
        ((abelianExtensionByZero j).obj G))
      ((ProEt.abelianExtensionByZero j).obj
        ((etaleToProEtPullback U AddCommGrpCat.{w}).obj G)) :=
  sorry

end

end AlgebraicGeometry.Scheme
