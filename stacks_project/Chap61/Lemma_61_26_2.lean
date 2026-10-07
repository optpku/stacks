module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap59.Definition_59_70_1_ExtensionByZero
public import stacks_project.Chap61.Definition_61_26_1_ExtensionByZero
public import stacks_project.Chap61.Lemma_61_26_2_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.26.2

Étale extension by zero commutes with inverse image along the
étale-to-pro-étale comparison of small sites.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

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

/-- Lemma 61.26.2: for an étale morphism `j : U ⟶ X` and an abelian sheaf `G`
on the small étale site of `U`, the sheaves `ε⁻¹ (j_! G)` and `j_! (ε⁻¹ G)`
on the small pro-étale site of `X` are isomorphic, where `ε⁻¹` is sheaf
pullback along `etaleToProEt` and the two extension-by-zero functors are the
étale and pro-étale `abelianExtensionByZero`. -/
@[stacks 09AF]
theorem abelianExtensionByZero_etaleProetale
    (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{w}) :
    IsIsomorphic
      ((etaleToProEtPullback X AddCommGrpCat.{w}).obj
        ((abelianExtensionByZero j).obj G))
      ((ProEt.abelianExtensionByZero j).obj
        ((etaleToProEtPullback U AddCommGrpCat.{w}).obj G)) :=
  sorry

/-- Étale abelian extension by zero commutes with inverse image along
`etaleToProEt` as functors on abelian sheaves. -/
theorem abelianExtensionByZero_etaleProetale_functor :
    IsIsomorphic
      (abelianExtensionByZero j ⋙ etaleToProEtPullback X AddCommGrpCat.{w})
      (etaleToProEtPullback U AddCommGrpCat.{w} ⋙
        ProEt.abelianExtensionByZero j) :=
  sorry

end

/-- Restriction along an étale morphism commutes with the étale-to-pro-étale
comparison of small sites. -/
theorem etaleRestriction_comp_etaleToProEt :
    etaleRestriction j ⋙ etaleToProEt X =
      etaleToProEt U ⋙ ProEt.restriction j :=
  sorry

end AlgebraicGeometry.Scheme
