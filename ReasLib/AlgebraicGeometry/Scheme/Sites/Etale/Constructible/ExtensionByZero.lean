module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u w

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}} (j : U ⟶ X)
variable [CompactSpace U] [QuasiSeparatedSpace U]
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [Etale j]

/-- The sheafified representable associated to an étale morphism is constructible on the
small étale site when restrictions are taken by canonical inverse image. -/
theorem sheafifiedRepresentable_isConstructibleEtaleSet
    [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) (Type (u + 1))]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))] :
    CategoryTheory.Sheaf.IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstant G)
      (X.smallEtaleTopology.sheafifiedRepresentable
        (MorphismProperty.Over.mk ⊤ j inferInstance)) := sorry

/-- The extension by zero of a finite constant abelian sheaf along an étale morphism is
constructible on the small étale site under canonical inverse-image restrictions. -/
theorem abelianExtensionByZero_constant_isConstructibleEtaleAddCommGrp
    {M : Type (u + 1)} [AddCommGroup M] [Finite M]
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasWeakSheafify U.smallEtaleTopology AddCommGrpCat.{u + 1}] :
    CategoryTheory.Sheaf.IsConstructibleEtaleAddCommGrp
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstantAddCommGrp G)
      ((abelianExtensionByZero j).obj
        ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (.of M))) := sorry

/-- The extension by zero of a finite constant module sheaf along an étale morphism is
constructible on the small étale site for a Noetherian coefficient ring. -/
theorem moduleExtensionByZero_constant_isConstructibleEtaleModule
    {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    {M : Type w} [AddCommGroup M] [Module Λ M] [Module.Finite Λ M]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
    [HasWeakSheafify U.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ (Y : Scheme.{u}), HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{w} Λ)]
    [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
      (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P] :
    CategoryTheory.Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((moduleExtensionByZero j).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{w} Λ)).obj
          (.of Λ M))) := sorry

end AlgebraicGeometry.Scheme
