module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleComparison
public import ReasLib.CategoryTheory.Sites.LocallyConstant.FinitePresentation
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Étale-to-pro-étale comparison of locally constant module sheaves

Canonical inverse image restricts to an equivalence on locally constant sheaves
with finitely presented module models over an arbitrary ring.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
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

/-- Inverse image along `etaleToProEt` preserves locally constant sheaves of
finitely presented `Λ`-modules. -/
instance etaleToProEtPullback_isLocallyConstantFinitePresentation
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w} Λ))
    [LocallyConstant.IsFinitePresentation F] :
    LocallyConstant.IsFinitePresentation
      ((etaleToProEtPullback X (ModuleCat.{max (u + 1) w} Λ)).obj F) :=
  sorry

/-- Locally constant finitely presented étale sheaves of `Λ`-modules are
carried into the corresponding pro-étale class by `ε⁻¹`. -/
theorem etaleToProEtPullback_locallyConstantFinitePresentation_le :
    (LocallyConstant.finitePresentation :
        ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w} Λ))) ≤
      ObjectProperty.inverseImage
        (LocallyConstant.finitePresentation :
          ObjectProperty (Sheaf (ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
        (etaleToProEtPullback X (ModuleCat.{max (u + 1) w} Λ)) := by
  intro F hF
  exact etaleToProEtPullback_isLocallyConstantFinitePresentation X Λ F

/-- Inverse image `ε⁻¹` along `etaleToProEt`, restricted to locally constant
sheaves of finitely presented `Λ`-modules. -/
def etaleToProEtPullback_locallyConstantFP :
    ObjectProperty.FullSubcategory
      (LocallyConstant.finitePresentation :
        ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w} Λ))) ⥤
      ObjectProperty.FullSubcategory
        (LocallyConstant.finitePresentation :
          ObjectProperty (Sheaf (ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) :=
  ObjectProperty.FullSubcategory.restrict
    (etaleToProEtPullback X (ModuleCat.{max (u + 1) w} Λ))
    (etaleToProEtPullback_locallyConstantFinitePresentation_le X Λ)

/-- Inverse image from the small étale site to the small pro-étale site induces an
equivalence on locally constant sheaves with finitely presented module models. -/
@[stacks 099Y]
instance etaleToProEtPullback_locallyConstantFP_isEquivalence :
    (etaleToProEtPullback_locallyConstantFP X Λ).IsEquivalence :=
  sorry

end AlgebraicGeometry.Scheme
