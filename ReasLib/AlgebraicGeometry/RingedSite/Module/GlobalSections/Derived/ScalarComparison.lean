module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Comparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite RingedSite.Hom

universe u

/-- Commutative global sections with the original bundled ring operations. -/
noncomputable instance instCommRingGlobalSectionsRing
    {X : RingedSite.{u, u, u}} [UnivLE.{u, u}]
    [h : Fact (∀ a b : globalSectionsRing X, a * b = b * a)] :
    CommRing (globalSectionsRing X) where
  toRing := inferInstance
  mul_comm := h.elim

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, u, u}}
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{u} X)]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{u} Y)]
variable [Fact (∀ a b : globalSectionsRing X, a * b = b * a)]
variable [Fact (∀ a b : globalSectionsRing Y, a * b = b * a)]
variable (g : X.Hom Y) [g.modulePushforward.{u}.IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{u} g) (ModuleQis.{u} X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{u} g) (ModuleQis.{u} Y)]
variable [DerivedAdjunction.HasPair.{u} g]

/-- The canonical scalar-extension/global-sections comparison. It is the
adjoint transpose of the pullback unit followed by the canonical comparison
between global sections and derived pushforward. No arbitrary comparison
morphism or assumed invertibility is supplied. -/
noncomputable def derivedScalarGlobalSectionsComparison (K : ModuleDerived.{u} Y) :
    (CategoryTheory.ModuleCat.derivedExtensionOfScalars (globalSectionsMap g).hom).obj
        ((moduleDerivedGlobalSections.{u} Y).obj K) ⟶
      (moduleDerivedGlobalSections.{u} X).obj ((modulePullbackDerived.{u} g).obj K) :=
  letI := moduleGlobalSectionsToModuleDerived_hasRightDerivedFunctor X
  letI := moduleGlobalSectionsToModuleDerived_hasRightDerivedFunctor Y
  ((CategoryTheory.ModuleCat.derivedExtensionRestrictionAdjunction
      (globalSectionsMap g).hom).homEquiv _ _).symm
    ((moduleDerivedGlobalSections.{u} Y).map ((moduleDerivedAdjunction.{u} g).unit.app K) ≫
      (ModuleSections.derivedGlobalSectionsPushforwardIso g).inv.app
        ((modulePullbackDerived.{u} g).obj K))

end RingedSite.Hom
