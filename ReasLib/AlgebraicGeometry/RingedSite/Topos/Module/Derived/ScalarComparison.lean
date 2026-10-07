module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.SectionsComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction

@[expose] public section

open CategoryTheory

universe uX vX uY vY w

namespace RingedSite.ToposHom

/-- Commutative global sections retaining the bundled ring's operations. -/
noncomputable instance globalSectionsCommRing
    (X : RingedSite.{uX, vX, w}) [UnivLE.{uX, w}]
    [h : Fact (∀ a b : Hom.globalSectionsRing X, a * b = b * a)] :
    CommRing (Hom.globalSectionsRing X) where
  toRing := inferInstance
  mul_comm := h.elim

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

/-- The canonical scalar-extension/global-sections map for an arbitrary
ringed-topos morphism. It is the scalar adjoint transpose of the derived
pullback unit, transported through the constructed sections comparison. -/
noncomputable def derivedScalarGlobalSectionsComparison (K : Hom.ModuleDerived.{w} Y) :
    (CategoryTheory.ModuleCat.derivedExtensionOfScalars f.globalSectionsMap.hom).obj
      ((Hom.moduleDerivedGlobalSections.{w} Y).obj K) ⟶
        (Hom.moduleDerivedGlobalSections.{w} X).obj (f.modulePullbackDerived.obj K) :=
  ((CategoryTheory.ModuleCat.derivedExtensionRestrictionAdjunction f.globalSectionsMap.hom).homEquiv _ _).symm
    ((Hom.moduleDerivedGlobalSections.{w} Y).map (f.moduleDerivedAdjunction.unit.app K) ≫
      f.derivedGlobalSectionsPushforwardIso.inv.app (f.modulePullbackDerived.obj K))

end RingedSite.ToposHom
