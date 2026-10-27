/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ExtensionByZero.LowerShriek
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ModuleSheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open CategoryTheory.GrothendieckTopology CategoryTheory.Functor.RightDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification
open Opposite AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section Sections

variable {S T : Scheme.{u}} (s : T ⟶ S) (Λ : Type u) [Ring Λ]
variable [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [((sheafSections S.smallEtaleTopology (ModuleCat.{u} Λ)).obj (op (globalEtale S))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModuleGamma Λ S))
  (HomologicalComplex.quasiIso (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [((sheafSections T.smallEtaleTopology (ModuleCat.{u} Λ)).obj (op (globalEtale T))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModuleGamma Λ T))
  (HomologicalComplex.quasiIso (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [HasDerivedCategory (ModuleCat.{u} Λ)]
variable [∀ F : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback s).op.HasLeftKanExtension F]

/-- Pullback of derived global sections is induced by the inverse-image adjunction unit. -/
@[irreducible]
def etaleDerivedGammaPullback :
    etaleDerivedGamma S Λ ⟶ etaleModuleDerivedInverseImage s Λ ⋙ etaleDerivedGamma T Λ :=
  (RightDerived.Cochain.functor (etaleModuleGamma Λ S)).rightDerivedDesc
    (RightDerived.Cochain.unit (etaleModuleGamma Λ S))
    (HomologicalComplex.quasiIso (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (etaleModuleDerivedInverseImage s Λ ⋙ etaleDerivedGamma T Λ)
    (whiskerRight
      (NatTrans.mapHomologicalComplex (etaleModuleGammaPullback Λ s) (ComplexShape.up ℤ))
      (DerivedCategory.Q : CochainComplex (ModuleCat.{u} Λ) ℤ ⥤ DerivedCategory (ModuleCat.{u} Λ)) ≫
    RightDerived.Cochain.ExactFirst.unit
      (ExactFunctor.of (Sheaf.smallEtaleInverseImage s (ModuleCat.{u} Λ)))
      (etaleModuleGamma Λ T))

end Sections

section CompactSupport

variable {k l : Type u} [Field k] [Field l] (Λ : Type u) [Ring Λ]
variable {X : SchemeOverField k} {X' : SchemeOverField l}
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [IsSeparated X'.hom] [Scheme.Hom.FiniteType X'.hom]
variable (P : Of (Spec (CommRingCat.of k)) X) (Q : Of (Spec (CommRingCat.of l)) X')
variable (s : Spec (CommRingCat.of l) ⟶ Spec (CommRingCat.of k))
variable (a : X'.left ⟶ X.left) (b : Q.obj.right.left ⟶ P.obj.right.left)
variable (hp : IsPullback b Q.obj.right.hom P.obj.right.hom s)
variable (hj : IsPullback a (Of.ι Q) (Of.ι P) b)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [hX : HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.left.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.left.smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X'.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X'.left.Etale, HasWeakSheafify (X'.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [hXprime : HasDerivedCategory (Sheaf X'.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify X'.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [X'.left.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.left.smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale, HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [hP : HasDerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Q.obj.right.left.Etale, HasWeakSheafify (Q.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [hQ : HasDerivedCategory (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Q.obj.right.left.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Q.obj.right.left.smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : (Spec (CommRingCat.of k)).Etale, HasWeakSheafify ((Spec (CommRingCat.of k)).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (Spec (CommRingCat.of k)).smallEtaleTopology AddCommGrpCat.{u}]
variable [(Spec (CommRingCat.of k)).smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [(Spec (CommRingCat.of k)).smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify (Spec (CommRingCat.of l)).smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : (Spec (CommRingCat.of l)).Etale, HasWeakSheafify ((Spec (CommRingCat.of l)).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (Spec (CommRingCat.of l)).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (Spec (CommRingCat.of l)).smallEtaleTopology AddCommGrpCat.{u}]
variable [(Spec (CommRingCat.of l)).smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [(Spec (CommRingCat.of l)).smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasDerivedCategory (ModuleCat.{u} Λ)]
variable [hQ_structKan : ∀ F : (Spec (CommRingCat.of l)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback Q.obj.right.hom).op.HasLeftKanExtension F]
variable [hP_structKan : ∀ F : (Spec (CommRingCat.of k)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback P.obj.right.hom).op.HasLeftKanExtension F]
variable [∀ F : (Spec (CommRingCat.of k)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback s).op.HasLeftKanExtension F]
variable [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback b).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback a).op.HasLeftKanExtension F]
variable [hP_openKan : ∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι P)).op.HasLeftKanExtension F]
variable [hQ_openKan : ∀ F : Q.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι Q)).op.HasLeftKanExtension F]
variable [hopenLeftKan : ∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι Q ≫ b)).op.HasLeftKanExtension F]
variable [hopenRightKan : ∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (a ≫ Of.ι P)).op.HasLeftKanExtension F]
variable [hstructLeftKan : ∀ F : (Spec (CommRingCat.of k)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Q.obj.right.hom ≫ s)).op.HasLeftKanExtension F]
variable [hstructRightKan : ∀ F : (Spec (CommRingCat.of k)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (b ≫ P.obj.right.hom)).op.HasLeftKanExtension F]
variable [hP_extensionKanModule : ∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [hP_extensionKanAdd : ∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [hP_extensionPreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions (etaleRestriction (Of.ι P)).op]
variable [(etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
variable [hQ_extensionKanModule : ∀ F : X'.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [hQ_extensionKanAdd : ∀ F : X'.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [hQ_extensionPreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions (etaleRestriction (Of.ι Q)).op]
variable [(etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]
variable [(etaleModulePushforward P.obj.right.hom Λ).Additive]
variable [HasRightDerivedFunctor (RightDerived.Cochain.toDerived (etaleModulePushforward P.obj.right.hom Λ))
  (HomologicalComplex.quasiIso (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [(etaleModulePushforward Q.obj.right.hom Λ).Additive]
variable [HasRightDerivedFunctor (RightDerived.Cochain.toDerived (etaleModulePushforward Q.obj.right.hom Λ))
  (HomologicalComplex.quasiIso (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ)).obj (op (globalEtale (Spec (CommRingCat.of k))))).Additive]
variable [HasRightDerivedFunctor (RightDerived.Cochain.toDerived (etaleModuleGamma Λ (Spec (CommRingCat.of k))))
  (HomologicalComplex.quasiIso (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [CompactSpace (Spec (CommRingCat.of k))] [QuasiSeparatedSpace (Spec (CommRingCat.of k))]
variable [((sheafSections (Spec (CommRingCat.of l)).smallEtaleTopology (ModuleCat.{u} Λ)).obj (op (globalEtale (Spec (CommRingCat.of l))))).Additive]
variable [HasRightDerivedFunctor (RightDerived.Cochain.toDerived (etaleModuleGamma Λ (Spec (CommRingCat.of l))))
  (HomologicalComplex.quasiIso (Sheaf (Spec (CommRingCat.of l)).smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [CompactSpace (Spec (CommRingCat.of l))] [QuasiSeparatedSpace (Spec (CommRingCat.of l))]

variable [hambientKanAdd : ∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback b).op.HasLeftKanExtension F]
variable [hambientPreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback b).op]
variable [hsourceKanAdd : ∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback a).op.HasLeftKanExtension F]
variable [hsourcePreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback a).op]

/-- Cartesian compactifications induce the canonical base-change map on compactly supported sections. -/
@[irreducible]
def etaleDerivedGammaCompactSupportBaseChange
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleDerivedGammaCompactSupport (Λ := Λ) P).obj K ⟶
    (etaleDerivedGammaCompactSupport (Λ := Λ) Q).obj
      ((etaleModuleDerivedInverseImage a Λ).obj K) :=
  (etaleDerivedGammaPullback s Λ).app ((etaleDerivedLowerShriek X P).obj K) ≫
  (etaleDerivedGamma (Spec (CommRingCat.of l)) Λ).map
    (etaleDerivedPushforwardBaseChange_app P.obj.right.hom s Q.obj.right.hom b hp Λ
      ((etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory.obj K)) ≫
  (etaleDerivedGamma (Spec (CommRingCat.of l)) Λ).map
    ((etaleDerivedPushforward Q.obj.right.hom).map
      ((etaleModuleDerivedInverseImage b Λ).map
          ((extensionByZeroDerivedIsoLowerShriekModule (Of.ι P) Λ).hom.app K) ≫
        lowerShriekModuleDerivedBaseChange_app (Of.ι P) b (Of.ι Q) a hj Λ K ≫
        (extensionByZeroDerivedIsoLowerShriekModule (Of.ι Q) Λ).inv.app
          ((etaleModuleDerivedInverseImage a Λ).obj K)))

end CompactSupport

end AlgebraicGeometry.Scheme.Etale

end
