/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Hom
public import stacks_project.Chap61.Lemma_61_19_1_Comparison

/-!
# Restricted inverse image of locally constant finitely presented sheaves

Inverse image `ε⁻¹` along `etaleToProEt` preserves locally constant sheaves of
finitely presented `Λ`-modules, and therefore restricts to a functor between
the corresponding full subcategories of sheaves on `X.Etale` and `X.ProEt`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Sheaf

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type w) [CommRing Λ]
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
        (etaleToProEtPullback X (ModuleCat.{max (u + 1) w} Λ)) :=
  sorry

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

end AlgebraicGeometry.Scheme

