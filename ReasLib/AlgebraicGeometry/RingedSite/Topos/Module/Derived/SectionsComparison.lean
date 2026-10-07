module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

@[expose] public section

open CategoryTheory ComplexShape

universe uX vX uY vY w

namespace RingedSite.ToposHom

-- Local instance justification (defeq pin): the derived presentation must be
-- the existing RingedSite.Hom.ModuleDerived, not a newly chosen localization.
attribute [local instance] Hom.moduleCat_hasDerivedCategory
-- Local instance justification (proof-local temporary data): homotopy lifts
-- use the existing canonical additivity theorem for module-valued sections.
attribute [local instance] Hom.moduleGlobalSectionsFunctor_additive
-- Local instance justification (defeq pin): units use the same existence
-- proof as Hom.moduleDerivedGlobalSections.
attribute [local instance] Hom.moduleGlobalSectionsToModuleDerived_hasRightDerivedFunctor

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{uX, w}] [UnivLE.{uY, w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} X)]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} Y)]
variable (f : ToposHom X Y)

/-- Exact restriction of global-section scalars on derived categories. -/
noncomputable abbrev globalSectionsRestrictionDerived :=
  f.globalSectionsRestriction.mapDerivedCategory

/-- The homotopy-level scalar-restricted sections functor. -/
noncomputable abbrev sectionsSource :=
  Hom.moduleGlobalSectionsToModuleDerived.{w} X ⋙ f.globalSectionsRestrictionDerived

/-- The homotopy-level direct image followed by sections. -/
noncomputable abbrev sectionsTarget :=
  f.modulePushforward.mapHomotopyCategory (up ℤ) ⋙ Hom.moduleGlobalSectionsToModuleDerived.{w} Y

/-- Derived sections followed by exact scalar restriction. -/
noncomputable abbrev sectionsSourceDerived :=
  Hom.moduleDerivedGlobalSections.{w} X ⋙ f.globalSectionsRestrictionDerived

/-- Derived direct image followed by derived sections. -/
noncomputable abbrev sectionsTargetDerived :=
  f.modulePushforwardDerived ⋙ Hom.moduleDerivedGlobalSections.{w} Y

/-- The source right-derived unit is the usual sections unit with scalars restricted. -/
noncomputable def sectionsSourceUnit :
    f.sectionsSource ⟶ Hom.moduleLocalization.{w} X ⋙ f.sectionsSourceDerived :=
  Functor.whiskerRight
    (Functor.totalRightDerivedUnit (Hom.moduleGlobalSectionsToModuleDerived.{w} X)
      (Hom.moduleLocalization.{w} X) (Hom.ModuleQis.{w} X))
    f.globalSectionsRestrictionDerived ≫ (Functor.associator _ _ _).hom

/-- The target unit first derives sections and then derives direct image. -/
noncomputable def sectionsTargetUnit :
    f.sectionsTarget ⟶ Hom.moduleLocalization.{w} X ⋙ f.sectionsTargetDerived :=
  Functor.whiskerLeft (f.modulePushforward.mapHomotopyCategory (up ℤ))
    (Functor.totalRightDerivedUnit (Hom.moduleGlobalSectionsToModuleDerived.{w} Y)
      (Hom.moduleLocalization.{w} Y) (Hom.ModuleQis.{w} Y)) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.totalRightDerivedUnit (modulePushforwardToDerived f)
        (Hom.moduleLocalization.{w} X) (Hom.ModuleQis.{w} X))
      (Hom.moduleDerivedGlobalSections.{w} Y) ≫ (Functor.associator _ _ _).hom

/-- Exact scalar restriction preserves the right-derived sections model. -/
noncomputable instance sectionsSource_isRightDerived :
    f.sectionsSourceDerived.IsRightDerivedFunctor f.sectionsSourceUnit (Hom.ModuleQis.{w} X) := sorry

/-- Direct image followed by sections computes derived sections on the source. -/
noncomputable instance sectionsTarget_isRightDerived :
    f.sectionsTargetDerived.IsRightDerivedFunctor f.sectionsTargetUnit (Hom.ModuleQis.{w} X) := sorry

/-- The underived sections isomorphism transported to homotopy categories. -/
noncomputable def sectionsHomotopyIso :
    (Hom.moduleGlobalSectionsFunctor.{w} X ⋙ f.globalSectionsRestriction).mapHomotopyCategory (up ℤ) ≅
      (f.modulePushforward ⋙ Hom.moduleGlobalSectionsFunctor.{w} Y).mapHomotopyCategory (up ℤ) where
  hom := NatTrans.mapHomotopyCategory f.moduleGlobalSectionsPushforwardIso.inv (up ℤ)
  inv := NatTrans.mapHomotopyCategory f.moduleGlobalSectionsPushforwardIso.hom (up ℤ)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Canonical homotopy-level comparison, including the exact restriction's
localization factorization. -/
noncomputable def sectionsHomotopyComparison : f.sectionsSource ≅ f.sectionsTarget :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((Hom.moduleGlobalSectionsFunctor.{w} X).mapHomotopyCategory (up ℤ))
      f.globalSectionsRestriction.mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (Hom.moduleGlobalSectionsFunctor.{w} X ⋙ f.globalSectionsRestriction)) (up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight f.sectionsHomotopyIso DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (f.modulePushforward ⋙ Hom.moduleGlobalSectionsFunctor.{w} Y)) (up ℤ)).symm
      DerivedCategory.Qh ≪≫ Functor.associator _ _ _

/-- The derived module-valued sections comparison induced by the actual
underived natural isomorphism and the specified right-derived units. -/
noncomputable def derivedGlobalSectionsPushforwardIso :
    f.sectionsSourceDerived ≅ f.sectionsTargetDerived :=
  Functor.rightDerivedNatIso f.sectionsSourceDerived f.sectionsTargetDerived
    f.sectionsSourceUnit f.sectionsTargetUnit (Hom.ModuleQis.{w} X) f.sectionsHomotopyComparison

end RingedSite.ToposHom
