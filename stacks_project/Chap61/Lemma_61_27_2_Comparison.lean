module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap61.Definition_61_27_1
public import stacks_project.Chap61.Definition_61_28_1_Pullback
public import stacks_project.Chap61.Lemma_61_19_1_Comparison

/-!
# Restricted inverse image of constructible module sheaves

Inverse image `ε⁻¹` along `etaleToProEt` preserves constructible sheaves of
`Λ`-modules, and therefore restricts to a functor between the corresponding
full subcategories of sheaves on `X.Etale` and `X.ProEt`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Sheaf

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

/-- Inverse image of a sheaf of `Λ`-modules along a scheme morphism, induced by
small étale base change. -/
abbrev etaleModuleRestrict {X Y : Scheme.{u}} {Λ : Type w} [Ring Λ] (f : Y ⟶ X)
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ, (smallEtalePullback f).op.HasLeftKanExtension P]
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ) :=
  ((smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
    X.smallEtaleTopology Y.smallEtaleTopology).obj F

/-- `etaleModuleRestrict` is the action of small étale sheaf pullback on objects. -/
theorem etaleModuleRestrict_def {X Y : Scheme.{u}} {Λ : Type w} [Ring Λ] (f : Y ⟶ X)
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ, (smallEtalePullback f).op.HasLeftKanExtension P]
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)) :
    etaleModuleRestrict f F =
      ((smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
        X.smallEtaleTopology Y.smallEtaleTopology).obj F :=
  sorry

variable (X : Scheme.{u}) (Λ : Type w) [Ring Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ Y : Scheme.{u}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.ProEt),
    HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
    (ProEt.baseChange f).op.HasLeftKanExtension P]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ, (etaleToProEt X).op.HasLeftKanExtension F]

/-- Constructible sheaves of `Λ`-modules on the small étale site of `X`, in the
sense of `IsConstructibleEtaleModule` with canonical restriction and finite-type
locally constant models. -/
abbrev constructibleEtaleModule :
    ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)) :=
  fun F ↦ IsConstructibleEtaleModule (fun {_} f ↦ etaleModuleRestrict f)
    (fun {_} G ↦ IsFiniteTypeLocallyConstantModule G) F

/-- Unfolding `constructibleEtaleModule` recovers the pinned étale constructibility
predicate. -/
theorem constructibleEtaleModule_iff
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)) :
    constructibleEtaleModule X Λ F ↔
      IsConstructibleEtaleModule (fun {_} f ↦ etaleModuleRestrict f)
        (fun {_} G ↦ IsFiniteTypeLocallyConstantModule G) F :=
  sorry

/-- Constructible sheaves of `Λ`-modules on the small pro-étale site of `X`, in the
sense of `IsConstructibleProEtaleModule` with canonical restriction and finite-type
locally constant models. -/
abbrev constructibleProEtaleModule :
    ObjectProperty (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) :=
  fun F ↦ IsConstructibleProEtaleModule (fun {_} f ↦ ProEt.moduleRestrict f)
    (fun {_} G ↦ IsFiniteTypeLocallyConstantModule G) F

/-- Unfolding `constructibleProEtaleModule` recovers the pinned pro-étale
constructibility predicate. -/
theorem constructibleProEtaleModule_iff
    (F : Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) :
    constructibleProEtaleModule X Λ F ↔
      IsConstructibleProEtaleModule (fun {_} f ↦ ProEt.moduleRestrict f)
        (fun {_} G ↦ IsFiniteTypeLocallyConstantModule G) F :=
  sorry

/-- Inverse image along `etaleToProEt` preserves constructible sheaves of
`Λ`-modules. -/
theorem etaleToProEtPullback_isConstructibleModule
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)}
    (hF : constructibleEtaleModule X Λ F) :
    constructibleProEtaleModule X Λ
      ((etaleToProEtPullback X (ModuleCat.{w} Λ)).obj F) :=
  sorry

/-- Constructible étale sheaves of `Λ`-modules are carried into the corresponding
pro-étale class by `ε⁻¹`. -/
theorem etaleToProEtPullback_constructibleModule_le :
    constructibleEtaleModule X Λ ≤
      ObjectProperty.inverseImage (constructibleProEtaleModule X Λ)
        (etaleToProEtPullback X (ModuleCat.{w} Λ)) :=
  sorry

/-- Inverse image `ε⁻¹` along `etaleToProEt`, restricted to constructible sheaves
of `Λ`-modules. -/
def etaleToProEtPullback_constructibleModule :
    (constructibleEtaleModule X Λ).FullSubcategory ⥤
      (constructibleProEtaleModule X Λ).FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict
    (etaleToProEtPullback X (ModuleCat.{w} Λ))
    (etaleToProEtPullback_constructibleModule_le X Λ)

/-- The underlying sheaf of the restricted inverse image is the ambient `ε⁻¹`. -/
theorem etaleToProEtPullback_constructibleModule_obj
    (F : (constructibleEtaleModule X Λ).FullSubcategory) :
    ((etaleToProEtPullback_constructibleModule X Λ).obj F).obj =
      (etaleToProEtPullback X (ModuleCat.{w} Λ)).obj F.obj :=
  sorry

end AlgebraicGeometry.Scheme

