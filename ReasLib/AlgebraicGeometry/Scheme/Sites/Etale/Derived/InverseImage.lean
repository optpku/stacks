/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coefficients
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section Preservation

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type u) [Ring Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [X.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [Y.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]

/-- Exact inverse image preserves torsion cohomology. -/
theorem etaleModuleDerivedInverseImage_isTorsion
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
    (hK : etaleDerivedIsTorsion K) :
    etaleDerivedIsTorsion ((etaleModuleDerivedInverseImage f Λ).obj K) := sorry

/-- Exact inverse image preserves every lower cohomological bound. -/
instance etaleModuleDerivedInverseImage_isGE
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
    (n : ℤ) [hK : K.IsGE n] :
    ((etaleModuleDerivedInverseImage f Λ).obj K).IsGE n := sorry

/-- Exact inverse image preserves compact-support admissibility. -/
theorem etaleModuleDerivedInverseImage_compactSupportAdmissible
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
    (hK : Derived.compactSupportAdmissible Y Λ K) :
    Derived.compactSupportAdmissible X Λ ((etaleModuleDerivedInverseImage f Λ).obj K) := by
  rcases hK with ⟨hT, n, hGE⟩ | hΛ
  · exact Or.inl ⟨etaleModuleDerivedInverseImage_isTorsion f Λ K hT,
      n, etaleModuleDerivedInverseImage_isGE f Λ K n (hK := hGE)⟩
  · exact Or.inr hΛ

end Preservation

section Square

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g) (Λ : Type u) [Ring Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X'.Etale, HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale, HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f' ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ f)).op.HasLeftKanExtension P]

/-- The canonical derived inverse-image comparison around a cartesian square. -/
@[irreducible]
def etaleModuleDerivedInverseImage_square :
    etaleModuleDerivedInverseImage g Λ ⋙ etaleModuleDerivedInverseImage f' Λ ≅
      etaleModuleDerivedInverseImage f Λ ⋙ etaleModuleDerivedInverseImage g' Λ :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
    (ExactFunctor.of (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)))
    (ExactFunctor.of (Sheaf.smallEtaleInverseImage f' (ModuleCat.{u} Λ)))).symm ≪≫
  Functor.MapDerivedCategory.functorIso
    (etaleModuleSheafPullback_square f g f' g' h_cart Λ) ≪≫
  ExactFunctor.MapDerivedCategory.compFunctorIso
    (ExactFunctor.of (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)))
    (ExactFunctor.of (Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)))

/-- The forward inverse-image comparison is the composite of the exact-derived comparisons. -/
theorem etaleModuleDerivedInverseImage_square_hom_app
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleModuleDerivedInverseImage_square f g f' g' h_cart Λ).hom.app K =
    (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)))
      (ExactFunctor.of (Sheaf.smallEtaleInverseImage f' (ModuleCat.{u} Λ)))).inv.app K ≫
    (Functor.MapDerivedCategory.functorIso
      (etaleModuleSheafPullback_square f g f' g' h_cart Λ)).hom.app K ≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)))
      (ExactFunctor.of (Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)))).hom.app K := by
  unfold etaleModuleDerivedInverseImage_square
  rfl

end Square

end AlgebraicGeometry.Scheme.Etale

end
