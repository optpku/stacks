/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings.Cochain
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.Assignment
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Left

/-! Identity comparisons for derived pullback of sheaves of modules. -/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SameSite.pullbackDerived

/-- Same-site module pullback along the identity is canonically the identity functor. -/
def pullbackIdIso (O : Sheaf J CommRingCat.{u}) :
    (sameSiteHom (𝟙 O)).modulePullback ≅ 𝟭 (ringedSiteModuleCategory.{u, u, u, u} J O) :=
  pullbackExtendIso (𝟙 O) ≪≫ extendIdIso O

/-- The homotopy-level identity-pullback model is canonically isomorphic to the
derived localization functor. -/
def idSourceIso (O : Sheaf J CommRingCat.{u}) :
    RingedSite.Hom.modulePullbackToDerived (sameSiteHom (𝟙 O)) ≅
      RingedSite.Hom.moduleLocalization (RingedSite.ofCommRingSheaf J O) :=
  Functor.isoWhiskerRight
      ((Functor.mapHomotopyCategoryIso (pullbackIdIso O)) ≪≫
        Functor.mapHomotopyCategoryIdIso (ringedSiteModuleCategory.{u, u, u, u} J O))
      (RingedSite.Hom.moduleLocalization (RingedSite.ofCommRingSheaf J O)) ≪≫
    Functor.leftUnitor _

/-- The canonical counit presenting the identity of the derived category as a left-derived
model of pullback along `𝟙 O`. -/
def idCounit (O : Sheaf J CommRingCat.{u}) :
    RingedSite.Hom.moduleLocalization (RingedSite.ofCommRingSheaf J O) ⋙
        𝟭 (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J O)) ⟶
      RingedSite.Hom.modulePullbackToDerived (sameSiteHom (𝟙 O)) :=
  (Functor.rightUnitor _).hom ≫ (idSourceIso O).inv

/-- The identity functor with `idCounit` has the canonical left-derived universal property. -/
theorem idFunctorIsLeftDerived (O : Sheaf J CommRingCat.{u}) :
    (𝟭 (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J O))).IsLeftDerivedFunctor
      (idCounit O) (RingedSite.Hom.ModuleQis (RingedSite.ofCommRingSheaf J O)) := sorry

/-- Derived pullback along the identity is canonically isomorphic to the identity functor. -/
def idIso (O : Sheaf J CommRingCat.{u}) :
    SameSite.pullbackDerived.{u, u, u, u} (𝟙 O) ≅
      𝟭 (RingedSite.Hom.ModuleDerived.{u} (RingedSite.ofCommRingSheaf J O)) :=
  @Functor.leftDerivedNatIso _ _ _ _ _ _
    (SameSite.pullbackDerived.{u, u, u, u} (𝟙 O))
    (𝟭 (RingedSite.Hom.ModuleDerived.{u} (RingedSite.ofCommRingSheaf J O)))
    (F := RingedSite.Hom.modulePullbackToDerived.{u} (sameSiteHom (𝟙 O)))
    (F' := RingedSite.Hom.modulePullbackToDerived.{u} (sameSiteHom (𝟙 O)))
    (L := RingedSite.Hom.moduleLocalization (RingedSite.ofCommRingSheaf J O))
    ((RingedSite.Hom.modulePullbackToDerived.{u} (sameSiteHom (𝟙 O))).totalLeftDerivedCounit
      (RingedSite.Hom.moduleLocalization (RingedSite.ofCommRingSheaf J O))
      (RingedSite.Hom.ModuleQis.{u} (RingedSite.ofCommRingSheaf J O)))
    (idCounit O) (RingedSite.Hom.ModuleQis.{u} (RingedSite.ofCommRingSheaf J O))
    inferInstance (idFunctorIsLeftDerived O) inferInstance (Iso.refl _)

/-- `idIso` identifies derived pullback along `𝟙 O` with the identity functor. -/
theorem idIso_hom_app (O : Sheaf J CommRingCat.{u})
    (K : RingedSite.Hom.ModuleDerived.{u} (RingedSite.ofCommRingSheaf J O)) :
    (idIso O).hom.app K =
      (@Functor.leftDerivedNatIso _ _ _ _ _ _
        (SameSite.pullbackDerived.{u, u, u, u} (𝟙 O))
        (𝟭 (RingedSite.Hom.ModuleDerived.{u} (RingedSite.ofCommRingSheaf J O)))
        (F := RingedSite.Hom.modulePullbackToDerived.{u} (sameSiteHom (𝟙 O)))
        (F' := RingedSite.Hom.modulePullbackToDerived.{u} (sameSiteHom (𝟙 O)))
        (L := RingedSite.Hom.moduleLocalization (RingedSite.ofCommRingSheaf J O))
        ((RingedSite.Hom.modulePullbackToDerived.{u} (sameSiteHom (𝟙 O))).totalLeftDerivedCounit
          (RingedSite.Hom.moduleLocalization (RingedSite.ofCommRingSheaf J O))
          (RingedSite.Hom.ModuleQis.{u} (RingedSite.ofCommRingSheaf J O)))
        (idCounit O) (RingedSite.Hom.ModuleQis.{u} (RingedSite.ofCommRingSheaf J O))
        inferInstance (idFunctorIsLeftDerived O) inferInstance (Iso.refl _)).hom.app K := rfl

end SameSite.pullbackDerived

end SheafOfModules.RingedSite
