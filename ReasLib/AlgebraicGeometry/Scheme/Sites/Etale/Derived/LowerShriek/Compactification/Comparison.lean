/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ExtensionByZero.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pushforward
public import Mathlib.GroupTheory.Torsion

/-!
# Comparison of compactification lower shriek with derived direct image

Each compactification determines a canonical comparison on all complexes.
Its independence of the compactification holds on bounded-below torsion
complexes, or on all complexes for a torsion coefficient ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (P : Of Y X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [h_interiorLeftKanExtension : ∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [h_extensionByZero_additive :
  (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
variable [h_extensionByZero_limits : PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
variable [h_extensionByZero_colimits : PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]

/-- Transport of `R(j ≫ f̄)_*` to `Rf_*` along the compactification triangle
`j ≫ f̄ = X.hom`. -/
def toPushforward_congr :
    (etaleDerivedPushforward (Of.ι P ≫ P.obj.right.hom) :
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ≅
      (etaleDerivedPushforward X.hom :
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  RightDerived.natIsoOfIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (HomologicalComplex.quasiIso
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (RightDerived.Cochain.unit
      (etaleModulePushforward (Of.ι P ≫ P.obj.right.hom) Λ))
    (RightDerived.Cochain.unit (etaleModulePushforward X.hom Λ))
    (isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (etaleModulePushforwardCongr (Λ := Λ) (Over.w P.obj.hom))
        (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))))

/-- Canonical comparison `Rf_! ⟶ Rf_*` of compactification models, obtained by
whiskering `moduleDerivedExtensionByZeroToDirectImage` with `R f̄_*` and inverting derived Leray. -/
def toPushforward :
    etaleDerivedLowerShriek X P ⟶
      (etaleDerivedPushforward X.hom :
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  whiskerRight (moduleDerivedExtensionByZeroToDirectImage (Λ := Λ) (Of.ι P))
      (etaleDerivedPushforward P.obj.right.hom :
        DerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ≫
    (asIso (etaleDerivedPushforwardComp (Of.ι P) P.obj.right.hom Λ)).inv ≫
    (toPushforward_congr X P).hom

/-- Unfolding of `toPushforward` as interior whiskering, inverted Leray, and
transport along `Over.w`. -/
theorem toPushforward_eq :
    toPushforward X P =
      whiskerRight (moduleDerivedExtensionByZeroToDirectImage (Λ := Λ) (Of.ι P))
          (etaleDerivedPushforward P.obj.right.hom :
            DerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ≫
        (asIso (etaleDerivedPushforwardComp (Of.ι P) P.obj.right.hom Λ)).inv ≫
        (toPushforward_congr X P).hom :=
  rfl

variable {Q : Of Y X} (φ : P ⟶ Q)
variable [HasSheafify Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Q.obj.right.left.Etale,
  HasWeakSheafify (Q.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]

variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]

variable [HasSheafCompose X.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose P.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose Q.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Q.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι P)).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι Q)).op]

/-- On objects of `D⁺_tors(X_étale, Λ)`, the comparison `Rf_! ⟶ Rf_*` is
independent of the compactification: along a morphism of compactifications
the two `toPushforward` maps agree after identifying the compactification
models of `Rf_!`. -/
theorem toPushforward_isoOfHom_of_isGE_isTorsion
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) (h_tors : etaleDerivedIsTorsion K) (n : ℤ)
    [DerivedCategory.IsGE K n] :
    (isoOfHom X Λ φ).app K ≫ (toPushforward X P).app K = (toPushforward X Q).app K :=
  sorry

/-- If `Λ` is a torsion ring, the comparison `Rf_! ⟶ Rf_*` is independent of
the compactification as a natural transformation on `D(X_étale, Λ)`. -/
theorem toPushforward_isoOfHom_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) :
    isoOfHom X Λ φ ≫ toPushforward X P = toPushforward X Q :=
  sorry

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

end
