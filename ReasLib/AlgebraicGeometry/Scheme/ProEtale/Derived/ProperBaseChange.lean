/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ProEtale.Reduction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleModuleComparison
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Proper base change

Proper base change for derived-complete complexes on small pro-étale sites.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.DerivedCategory
open ComplexShape
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt
open AlgebraicGeometry.Scheme.ProetaleDerived
open RingedSite.Hom.ModuleDerived
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable {Λ : Type (u + 1)} [CommRing Λ]
variable [UnivLE.{u + 1, u + 1}]
variable [∀ Z : Scheme.{u}, HasWeakSheafify (ProEt.topology Z) CommRingCat.{u + 1}]
variable [∀ Z : Scheme.{u}, HasWeakSheafify (ProEt.topology Z) RingCat.{u + 1}]
variable [∀ Z : Scheme.{u}, HasWeakSheafify (ProEt.topology Z) (Type (u + 1))]
variable [∀ Z : Scheme.{u}, HasWeakSheafify (ProEt.topology Z) AddCommGrpCat.{u + 1}]
variable [∀ Z : Scheme.{u},
    (ProEt.topology Z).HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
variable [∀ Z : Scheme.{u},
    (ProEt.topology Z).HasSheafCompose (CategoryTheory.forget RingCat.{u + 1})]
variable [∀ Z : Scheme.{u},
    (ProEt.topology Z).HasSheafCompose (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})]
variable [∀ Z : Scheme.{u},
    (ProEt.topology Z).PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
variable [∀ Z : Scheme.{u},
    (ProEt.topology Z).PreservesSheafification (CategoryTheory.forget RingCat.{u + 1})]
variable [∀ Z : Scheme.{u}, (ProEt.topology Z).WEqualsLocallyBijective RingCat.{u + 1}]
variable [∀ Z : Scheme.{u}, (ProEt.topology Z).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable [∀ Z : Scheme.{u}, HasGlobalSectionsFunctor (ProEt.topology Z) (Type (u + 1))]
variable [∀ Z : Scheme.{u},
    LocallySmall (SheafOfModules (Sheaf.ringSheafOfComm
      (constantCoefficientRing Z Λ)))]
variable [∀ Z : Scheme.{u},
    WellPowered (SheafOfModules (Sheaf.ringSheafOfComm
      (constantCoefficientRing Z Λ)))]
variable [∀ Z : Scheme.{u}, ∀ U : Z.ProEt,
    HasWeakSheafify ((ProEt.topology Z).over U) AddCommGrpCat.{u + 1}]
variable [∀ Z : Scheme.{u}, ∀ U : Z.ProEt,
    ((ProEt.topology Z).over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable [HasWeakSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify (ProEt.topology X') (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify (ProEt.topology Y') (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [Abelian (Sheaf (ProEt.topology X') (ModuleCat.{u + 1} Λ))]
variable [Abelian (Sheaf (ProEt.topology Y') (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X') (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology Y') (ModuleCat.{u + 1} Λ))]
variable [CategoryWithHomology (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange f).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange f).sheafPullback (Type (u + 1)) (ProEt.topology Y) (ProEt.topology X))]
variable [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange g).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange g).sheafPullback (Type (u + 1)) (ProEt.topology Y) (ProEt.topology Y'))]
variable [∀ P : Y'.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange f').op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange f').sheafPullback (Type (u + 1)) (ProEt.topology Y') (ProEt.topology X'))]
variable [∀ P : X.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange g').op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange g').sheafPullback (Type (u + 1)) (ProEt.topology X) (ProEt.topology X'))]
variable [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange (g' ≫ f)).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange (g' ≫ f)).sheafPullback (Type (u + 1)) (ProEt.topology Y) (ProEt.topology X'))]
variable [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange (f' ≫ g)).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange (f' ≫ g)).sheafPullback (Type (u + 1)) (ProEt.topology Y) (ProEt.topology X'))]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient f Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient g Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient f' Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient g' Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (RingedSite.ToposHom.comp (ofConstantCoefficient g' Λ)
      (ofConstantCoefficient f Λ)).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (RingedSite.ToposHom.comp (ofConstantCoefficient f' Λ)
      (ofConstantCoefficient g Λ)).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient (g' ≫ f) Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient (f' ≫ g) Λ).structureMap).IsRightAdjoint]
variable [(ofConstantCoefficient f Λ).HasModulePullbackDerived]
variable [(ofConstantCoefficient f Λ).HasModulePushforwardDerived]
variable [(ofConstantCoefficient g Λ).HasModulePullbackDerived]
variable [(ofConstantCoefficient g Λ).HasModulePushforwardDerived]
variable [(ofConstantCoefficient f' Λ).HasModulePullbackDerived]
variable [(ofConstantCoefficient f' Λ).HasModulePushforwardDerived]
variable [(ofConstantCoefficient g' Λ).HasModulePullbackDerived]
variable [(RingedSite.ToposHom.comp (ofConstantCoefficient f' Λ)
    (ofConstantCoefficient g Λ)).HasModulePullbackDerived]
variable [(RingedSite.ToposHom.comp (ofConstantCoefficient g' Λ)
    (ofConstantCoefficient f Λ)).HasModulePullbackDerived]
variable [(ofConstantCoefficient f Λ).modulePullback.Additive]
variable [(ofConstantCoefficient g Λ).modulePullback.Additive]
variable [(ofConstantCoefficient f' Λ).modulePullback.Additive]
variable [(ofConstantCoefficient g' Λ).modulePullback.Additive]
variable [(RingedSite.ToposHom.comp (ofConstantCoefficient f' Λ)
    (ofConstantCoefficient g Λ)).modulePullback.Additive]
variable [(RingedSite.ToposHom.comp (ofConstantCoefficient g' Λ)
    (ofConstantCoefficient f Λ)).modulePullback.Additive]
variable [(baseChange f ⋙ baseChange g').IsContinuous
    (ProEt.topology Y) (ProEt.topology X')]
variable [(baseChange g ⋙ baseChange f').IsContinuous
    (ProEt.topology Y) (ProEt.topology X')]
variable [(@Functor.Homotopy.toDerived _ _ _ _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ)))
    (ofConstantCoefficient f Λ).modulePullback inferInstance).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(@Functor.Homotopy.toDerived _ _ _ _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (ProEt.topology Y') (constantCoefficientRing Y' Λ)))
    (ofConstantCoefficient g Λ).modulePullback inferInstance).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(@Functor.Homotopy.toDerived _ _ _ _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (ProEt.topology X') (constantCoefficientRing X' Λ)))
    (ofConstantCoefficient f' Λ).modulePullback inferInstance).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(@Functor.Homotopy.toDerived _ _ _ _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (ProEt.topology X') (constantCoefficientRing X' Λ)))
    (ofConstantCoefficient g' Λ).modulePullback inferInstance).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(@Functor.Homotopy.toDerived _ _ _ _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (ProEt.topology X') (constantCoefficientRing X' Λ)))
    (RingedSite.ToposHom.comp (ofConstantCoefficient f' Λ)
      (ofConstantCoefficient g Λ)).modulePullback inferInstance).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [(@Functor.Homotopy.toDerived _ _ _ _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (ProEt.topology X') (constantCoefficientRing X' Λ)))
    (RingedSite.ToposHom.comp (ofConstantCoefficient g' Λ)
      (ofConstantCoefficient f Λ)).modulePullback inferInstance).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
variable [RingedSite.ToposHom.HasModuleDerivedAdjunction (ofConstantCoefficient f Λ)]
variable [RingedSite.ToposHom.HasModuleDerivedAdjunction (ofConstantCoefficient f' Λ)]
variable [RingedSite.ToposHom.HasModuleDerivedAdjunction (ofConstantCoefficient g Λ)]

/-- The completed derived base-change morphism
`Lg_comp^* Rf_* K ⟶ Rf'_* L(g')_comp^* K` of a cartesian square, using supplied completion reflectors. -/
def completedDerivedBaseChangeHomWithReflectors (h_cart : IsPullback g' f' f g) (I : Ideal Λ)
    (RX : ObjectProperty.Reflector
      (derivedCompleteObjectProperty (coefficientIdeal X' Λ I)))
    (RY : ObjectProperty.Reflector
      (derivedCompleteObjectProperty (coefficientIdeal Y' Λ I)))
    [IsIso (modulePullbackDerivedCompComparison g Λ f')]
    [IsIso (modulePullbackDerivedCompComparison f Λ g')]
    (K :
      (derivedCompleteObjectProperty (coefficientIdeal X Λ I)).FullSubcategory) :
    (DerivedComplete.pullback (ofConstantCoefficient g Λ)
      (coefficientIdeal Y Λ I) RY).obj ((completedPushforward f Λ I).obj K) ⟶
      (completedPushforward f' Λ I).obj ((DerivedComplete.pullback (ofConstantCoefficient g' Λ)
        (coefficientIdeal X Λ I) RX).obj K) :=
  (RY.adjunction.homEquiv
      ((modulePullbackDerived (ofConstantCoefficient g Λ)).obj
        ((modulePushforwardDerived (ofConstantCoefficient f Λ)).obj K.obj))
      ((completedPushforward f' Λ I).obj
        ((DerivedComplete.pullback (ofConstantCoefficient g' Λ)
          (coefficientIdeal X Λ I) RX).obj K))).symm
    (derivedBaseChangeMap
        (modulePullbackDerived (ofConstantCoefficient f Λ))
        (modulePullbackDerived (ofConstantCoefficient f' Λ))
        (modulePullbackDerived (ofConstantCoefficient g Λ))
        (modulePullbackDerived (ofConstantCoefficient g' Λ))
        (modulePushforwardDerived (ofConstantCoefficient f Λ))
        (modulePushforwardDerived (ofConstantCoefficient f' Λ))
        (RingedSite.ToposHom.moduleDerivedAdjunction (ofConstantCoefficient f Λ))
        (RingedSite.ToposHom.moduleDerivedAdjunction (ofConstantCoefficient f' Λ))
        (modulePullbackDerivedSquareIso f Λ g f' g' h_cart) K.obj ≫
      (modulePushforwardDerived (ofConstantCoefficient f' Λ)).map
        (RX.unit.app
          ((modulePullbackDerived (ofConstantCoefficient g' Λ)).obj K.obj)))

omit [HasWeakSheafify (ProEt.topology X') (ModuleCat.{u + 1} Λ)]
    [Abelian (Sheaf (ProEt.topology X') (ModuleCat.{u + 1} Λ))]
    [HasDerivedCategory (Sheaf (ProEt.topology X') (ModuleCat.{u + 1} Λ))]
    [CategoryWithHomology (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
    [(SheafOfModules.restrictScalars
      (ofConstantCoefficient (g' ≫ f) Λ).structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars
      (ofConstantCoefficient (f' ≫ g) Λ).structureMap).IsRightAdjoint] in
/-- Transposing the completed derived base-change morphism across the target reflection
adjunction gives the ordinary derived base-change morphism followed by the pushforward
of the source reflection unit. -/
theorem completedDerivedBaseChangeHomWithReflectors_spec (h_cart : IsPullback g' f' f g) (I : Ideal Λ)
    (RX : ObjectProperty.Reflector
      (derivedCompleteObjectProperty (coefficientIdeal X' Λ I)))
    (RY : ObjectProperty.Reflector
      (derivedCompleteObjectProperty (coefficientIdeal Y' Λ I)))
    [IsIso (modulePullbackDerivedCompComparison g Λ f')]
    [IsIso (modulePullbackDerivedCompComparison f Λ g')]
    (K :
      (derivedCompleteObjectProperty (coefficientIdeal X Λ I)).FullSubcategory) :
  (RY.adjunction.homEquiv
      ((modulePullbackDerived (ofConstantCoefficient g Λ)).obj
        ((modulePushforwardDerived (ofConstantCoefficient f Λ)).obj K.obj))
      ((completedPushforward f' Λ I).obj
        ((DerivedComplete.pullback (ofConstantCoefficient g' Λ)
          (coefficientIdeal X Λ I) RX).obj K)))
    (completedDerivedBaseChangeHomWithReflectors f g f' g' h_cart I RX RY K) =
    derivedBaseChangeMap
        (modulePullbackDerived (ofConstantCoefficient f Λ))
        (modulePullbackDerived (ofConstantCoefficient f' Λ))
        (modulePullbackDerived (ofConstantCoefficient g Λ))
        (modulePullbackDerived (ofConstantCoefficient g' Λ))
        (modulePushforwardDerived (ofConstantCoefficient f Λ))
        (modulePushforwardDerived (ofConstantCoefficient f' Λ))
        (RingedSite.ToposHom.moduleDerivedAdjunction (ofConstantCoefficient f Λ))
        (RingedSite.ToposHom.moduleDerivedAdjunction (ofConstantCoefficient f' Λ))
        (modulePullbackDerivedSquareIso f Λ g f' g' h_cart) K.obj ≫
      (modulePushforwardDerived (ofConstantCoefficient f' Λ)).map
        (RX.unit.app
          ((modulePullbackDerived (ofConstantCoefficient g' Λ)).obj K.obj)) :=
  Equiv.apply_symm_apply _ _

/-- For a proper morphism of schemes, a cartesian base-change
square, a Noetherian coefficient ring Λ with ideal I such that Λ ⧸ I is torsion,
and a derived-complete object K of D(X_proétale, Λ) whose reductions
K ⊗^L underline(Λ ⧸ I^n) are bounded below with cohomology sheaves coming from
X_étale, and with each Λ ⧸ I^n a perfect Λ-module, the completed derived
base-change map Lg_comp^* Rf_* K ⟶ Rf'_* L(g')_comp^* K is an isomorphism. -/
@[stacks 09C9]
theorem completedDerivedBaseChange_isIso_of_isProper_withReflectors
    [IsNoetherianRing Λ] [IsProper f] (h_cart : IsPullback g' f' f g) (I : Ideal Λ)
    (RX : ObjectProperty.Reflector
      (derivedCompleteObjectProperty (coefficientIdeal X' Λ I)))
    (RY : ObjectProperty.Reflector
      (derivedCompleteObjectProperty (coefficientIdeal Y' Λ I)))
    (h_torsion : AddMonoid.IsTorsion (Λ ⧸ I))
    (h_perf : ∀ n, ModuleCat.IsPerfect (ModuleCat.of Λ (Λ ⧸ I ^ n)))
    (K : ProetaleDerived X Λ)
    (hK : IsDerivedCompleteWithRespectTo K I)
    [(coefficientIdeal X Λ I :
        SheafOfModules.RingedSite.ringedSiteModuleCategory
          (ProEt.topology X) (constantCoefficientRing X Λ)).IsFiniteType]
    [(coefficientIdeal X' Λ I :
        SheafOfModules.RingedSite.ringedSiteModuleCategory
          (ProEt.topology X') (constantCoefficientRing X' Λ)).IsFiniteType]
    [(coefficientIdeal Y' Λ I :
        SheafOfModules.RingedSite.ringedSiteModuleCategory
          (ProEt.topology Y') (constantCoefficientRing Y' Λ)).IsFiniteType]
    [IsIso (modulePullbackDerivedCompComparison g Λ f')]
    [IsIso (modulePullbackDerivedCompComparison f Λ g')]
    [∀ n : ℕ, HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n))]
    [∀ n : ℕ,
      HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))]
    [∀ n : ℕ, (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [∀ n : ℕ, (Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]
    [∀ n : ℕ, HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ n))]
    [∀ n : ℕ,
      HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))]
    [∀ (n : ℕ) (F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ n)),
      (etaleToProEt X).op.HasLeftKanExtension F]
    (h_bdd : ∀ n : ℕ, IsBoundedBelow (proEtReduction I n K))
    (h_etale : ∀ n : ℕ,
      cohomologyIn (etaleToProEtModuleEssImage X (Λ ⧸ I ^ n)) (proEtReduction I n K)) :
    IsIso
      (completedDerivedBaseChangeHomWithReflectors f g f' g' h_cart I RX RY
        (toConstantComplete Λ I K hK)) := sorry

end AlgebraicGeometry.Scheme.ProEt

end

end
