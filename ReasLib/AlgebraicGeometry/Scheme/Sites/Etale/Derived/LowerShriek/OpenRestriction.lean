/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.OpenRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ExtensionByZero.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

variable {Y : Scheme.{u}} (X : Over Y) (P : Compactification.Of Y X)
variable (W : X.left.Opens) (hW : IsCompact (W : Set X.left))
variable (Λ : Type u) [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [HasSheafify W.toScheme.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ T : W.toScheme.Etale,
  HasWeakSheafify (W.toScheme.smallEtaleTopology.over T) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf W.toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : W.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction W.ι).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero W.ι (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero W.ι (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero W.ι (ModuleCat.{u} Λ))]
variable [∀ F : W.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (W.ι ≫ Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (W.ι ≫ Compactification.Of.ι P) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (W.ι ≫ Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero (W.ι ≫ Compactification.Of.ι P) (ModuleCat.{u} Λ))]

/-- Extension by zero from a quasi-compact open followed by derived lower
shriek identifies with derived lower shriek for the restricted morphism,
using the compactification with unchanged proper ambient scheme. -/
def openRestrictionIso :
    etaleDerivedExtensionByZero W.ι Λ ⋙ etaleDerivedLowerShriek X P ≅
      -- These inherited instances identify the unchanged sites through the
      -- compactification constructors; callers use the comparison with inferred instances.
      @etaleDerivedLowerShriek Y (Over.mk (W.ι ≫ X.hom)) Λ inferInstance
        (Compactification.Of.restrictOpen P W hW)
        (inferInstanceAs (HasSheafify W.toScheme.smallEtaleTopology (ModuleCat.{u} Λ)))
        (inferInstanceAs (HasDerivedCategory (Sheaf W.toScheme.smallEtaleTopology (ModuleCat.{u} Λ))))
        (inferInstanceAs (HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)))
        (inferInstanceAs (HasDerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))))
        (inferInstanceAs (HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)))
        (inferInstanceAs (HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))))
        (inferInstanceAs (∀ F : W.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
            (etaleRestriction (W.ι ≫ Compactification.Of.ι P)).op.HasLeftKanExtension F))
        (inferInstanceAs ((etaleExtensionByZero (W.ι ≫ Compactification.Of.ι P) (ModuleCat.{u} Λ)).Additive))
        (inferInstanceAs (PreservesFiniteLimits
            (etaleExtensionByZero (W.ι ≫ Compactification.Of.ι P) (ModuleCat.{u} Λ))))
        (inferInstanceAs (PreservesFiniteColimits
            (etaleExtensionByZero (W.ι ≫ Compactification.Of.ι P) (ModuleCat.{u} Λ))))
        (inferInstanceAs (((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
            (ModuleCat.{u} Λ) Y.smallEtaleTopology P.obj.right.left.smallEtaleTopology).Additive))
        (inferInstanceAs (HasRightDerivedFunctor
            (RightDerived.Cochain.toDerived
              ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
                (ModuleCat.{u} Λ) Y.smallEtaleTopology P.obj.right.left.smallEtaleTopology))
            (HomologicalComplex.quasiIso
              (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
              (ComplexShape.up ℤ)))) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (etaleDerivedExtensionByZeroCompIso W.ι (Compactification.Of.ι P) Λ)
      (etaleDerivedPushforward P.obj.right.hom)

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

end
