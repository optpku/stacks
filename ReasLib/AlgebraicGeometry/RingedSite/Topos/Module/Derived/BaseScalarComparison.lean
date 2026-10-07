module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.ScalarComparison
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition

@[expose] public section

open CategoryTheory

universe uX vX uY vY w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{uX, w}] [UnivLE.{uY, w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} X)]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} Y)]
variable [Fact (∀ a b : Hom.globalSectionsRing X, a * b = b * a)]
variable [Fact (∀ a b : Hom.globalSectionsRing Y, a * b = b * a)]
variable (f : ToposHom X Y)
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
variable [HasModulePullbackDerived f] [HasModuleDerivedAdjunction f]
variable {R S : Type w} [CommRing R] [CommRing S]
variable (α : R →+* Hom.globalSectionsRing Y) (β : S →+* Hom.globalSectionsRing X)
variable (σ : R →+* S) (h : f.globalSectionsMap.hom.comp α = β.comp σ)

/-- The equality of actual base actions identifies the two iterated
restrictions of scalars; no arbitrary natural isomorphism is supplied. -/
noncomputable def baseRestrictionIso :
    f.globalSectionsRestrictionDerived ⋙ CategoryTheory.ModuleCat.derivedRestrictionOfScalars α ≅
      CategoryTheory.ModuleCat.derivedRestrictionOfScalars β ⋙
        CategoryTheory.ModuleCat.derivedRestrictionOfScalars σ :=
  (CategoryTheory.ModuleCat.DerivedRestriction.compIso α f.globalSectionsMap.hom).symm ≪≫
    eqToIso (congrArg CategoryTheory.ModuleCat.derivedRestrictionOfScalars h) ≪≫
    CategoryTheory.ModuleCat.DerivedRestriction.compIso σ β

/-- Base-linear pullback on derived sections. The map is the pullback unit
followed by the canonical sections comparison and the prescribed base action. -/
noncomputable def baseSectionsPullback (K : Hom.ModuleDerived.{w} Y) :
    (CategoryTheory.ModuleCat.derivedRestrictionOfScalars α).obj
      ((Hom.moduleDerivedGlobalSections.{w} Y).obj K) ⟶
    (CategoryTheory.ModuleCat.derivedRestrictionOfScalars σ).obj
      ((CategoryTheory.ModuleCat.derivedRestrictionOfScalars β).obj
        ((Hom.moduleDerivedGlobalSections.{w} X).obj (f.modulePullbackDerived.obj K))) :=
  (CategoryTheory.ModuleCat.derivedRestrictionOfScalars α).map
    ((Hom.moduleDerivedGlobalSections.{w} Y).map (f.moduleDerivedAdjunction.unit.app K) ≫
      f.derivedGlobalSectionsPushforwardIso.inv.app (f.modulePullbackDerived.obj K)) ≫
    (f.baseRestrictionIso α β σ h).hom.app
      ((Hom.moduleDerivedGlobalSections.{w} X).obj (f.modulePullbackDerived.obj K))

/-- Canonical base change on cohomology over the given base rings. This is
the scalar adjoint transpose of the constructed base-linear pullback map. -/
noncomputable def baseScalarComparison (K : Hom.ModuleDerived.{w} Y) :
    (CategoryTheory.ModuleCat.derivedExtensionOfScalars σ).obj
      ((CategoryTheory.ModuleCat.derivedRestrictionOfScalars α).obj
        ((Hom.moduleDerivedGlobalSections.{w} Y).obj K)) ⟶
    (CategoryTheory.ModuleCat.derivedRestrictionOfScalars β).obj
      ((Hom.moduleDerivedGlobalSections.{w} X).obj (f.modulePullbackDerived.obj K)) :=
  ((CategoryTheory.ModuleCat.derivedExtensionRestrictionAdjunction σ).homEquiv _ _).symm
    (f.baseSectionsPullback α β σ h K)

end RingedSite.ToposHom
