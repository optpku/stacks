/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Comparison
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition

/-!
# Comparisons of derived module pullbacks
-/

-- Private comparison constructions supply the explicit public isomorphisms.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor ComplexShape
open RingedSite
open Sheaf.InternalModule (underlyingApp)

noncomputable section

universe u v w uA vA

namespace CategoryTheory.SimplicialSites

/-- Identity on cochain complexes induces the identity on the homotopy category. -/
private def mapHomotopyCategoryIdIso {A : Type uA} [Category.{vA} A] [Preadditive A] :
    (𝟭 A).mapHomotopyCategory (up ℤ) ≅ 𝟭 (HomotopyCategory A (up ℤ)) :=
  Quotient.natIsoLift _
    (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso A (up ℤ))
      (HomotopyCategory.quotient A (up ℤ)))

section ToposHomComparisons

variable {X Y Z : RingedSite.{u, v, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Z.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable (f : ToposHom X Y) (g : ToposHom Y Z) (h : ToposHom X Z)
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} g.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} h.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (f.comp g).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (ToposHom.id X).structureMap).IsRightAdjoint]
variable [ToposHom.HasModulePullbackDerived f]
variable [ToposHom.HasModulePullbackDerived g]
variable [ToposHom.HasModulePullbackDerived h]

variable (hcomp : h.modulePullback ≅ g.modulePullback ⋙ f.modulePullback)

/-- Homotopy-to-derived pullback along `h` identifies with the iterated homotopy-level model of
`g` then `f`. -/
def derivedPullbackCompToDerivedIso :
    ToposHom.modulePullbackToDerived h ≅
      g.modulePullbackHomotopy ⋙ ToposHom.modulePullbackToDerived f :=
  Functor.isoWhiskerRight (@Functor.mapHomotopyCategoryCompIso _ _ _ _ _ _ _ _ _ _
        g.modulePullback f.modulePullback h.modulePullback hcomp.symm
        (ToposHom.modulePullback_additive g) (ToposHom.modulePullback_additive f)
        (ToposHom.modulePullback_additive h) (up ℤ)).symm
      (Hom.moduleLocalization X) ≪≫
    Functor.associator _ _ _

/-- Iterated counit from `Lf_f^* ∘ Lf_g^*` to the homotopy-level model of `g` then `f`. -/
def derivedPullbackCompCounit :
    Hom.moduleLocalization Z ⋙ (g.modulePullbackDerived ⋙ f.modulePullbackDerived) ⟶
      g.modulePullbackHomotopy ⋙ ToposHom.modulePullbackToDerived f :=
  (Functor.associator (Hom.moduleLocalization Z) g.modulePullbackDerived
      f.modulePullbackDerived).inv ≫
    Functor.whiskerRight
      ((ToposHom.modulePullbackToDerived g).totalLeftDerivedCounit
        (Hom.moduleLocalization Z) (Hom.ModuleQis Z))
      f.modulePullbackDerived ≫
    (Functor.associator (g.modulePullbackHomotopy)
      (Hom.moduleLocalization Y) f.modulePullbackDerived).hom ≫
    Functor.whiskerLeft (g.modulePullbackHomotopy)
      ((ToposHom.modulePullbackToDerived f).totalLeftDerivedCounit
        (Hom.moduleLocalization Y) (Hom.ModuleQis Y))

/-- Canonical comparison `Lf_f^* ∘ Lf_g^* ⟶ Lf_h^*` of derived module pullbacks, for an underived
identification `h^* ≅ g^* ⋙ f^*`. -/
def derivedPullbackCompComparisonOf :
    g.modulePullbackDerived ⋙ f.modulePullbackDerived ⟶ h.modulePullbackDerived :=
  h.modulePullbackDerived.leftDerivedLift
    ((ToposHom.modulePullbackToDerived h).totalLeftDerivedCounit
      (Hom.moduleLocalization Z) (Hom.ModuleQis Z))
    (Hom.ModuleQis Z) (g.modulePullbackDerived ⋙ f.modulePullbackDerived)
    (derivedPullbackCompCounit f g ≫ (derivedPullbackCompToDerivedIso f g h hcomp).inv)

/-- Component of `derivedPullbackCompComparisonOf` on an object of `D(O_Z)`. -/
theorem derivedPullbackCompComparisonOf_app (K : Hom.ModuleDerived.{w} Z) :
    (derivedPullbackCompComparisonOf f g h hcomp).app K =
      (h.modulePullbackDerived.leftDerivedLift
        ((ToposHom.modulePullbackToDerived h).totalLeftDerivedCounit
          (Hom.moduleLocalization Z) (Hom.ModuleQis Z))
        (Hom.ModuleQis Z) (g.modulePullbackDerived ⋙ f.modulePullbackDerived)
        (derivedPullbackCompCounit f g ≫ (derivedPullbackCompToDerivedIso f g h hcomp).inv)).app K :=
  sorry

/-- The composition comparison of derived module pullbacks is an isomorphism. -/
theorem derivedPullbackCompComparisonOf_isIso :
    IsIso (derivedPullbackCompComparisonOf f g h hcomp) :=
  sorry

end ToposHomComparisons

section ToposHomIdComparisons

variable {X : RingedSite.{u, v, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable (h : ToposHom X X)
variable [(SheafOfModules.restrictScalars.{w} h.structureMap).IsRightAdjoint]
variable [ToposHom.HasModulePullbackDerived h]
variable (hid : h.modulePullback ≅ 𝟭 (SheafOfModules.{w} X.structureSheaf))

/-- Homotopy-to-derived pullback along `h` is localization `Qh` after an underived identity
identification. -/
def derivedPullbackIdSourceIsoOf :
    ToposHom.modulePullbackToDerived h ≅ Hom.moduleLocalization X :=
  Functor.isoWhiskerRight
      (@Functor.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
          (ToposHom.modulePullback_additive h) inferInstance hid ≪≫
        mapHomotopyCategoryIdIso)
      (Hom.moduleLocalization X) ≪≫
    Functor.leftUnitor _

/-- Counit presenting the identity of `D(O_X)` as a left-derived model of `Lf_h^*`. -/
def derivedPullbackIdCounitOf :
    Hom.moduleLocalization X ⋙ 𝟭 (Hom.ModuleDerived.{w} X) ⟶
      ToposHom.modulePullbackToDerived h :=
  (Functor.rightUnitor (Hom.moduleLocalization X)).hom ≫
    (derivedPullbackIdSourceIsoOf h hid).inv

/-- Canonical comparison `id ⟶ Lf_h^*` of derived module pullbacks. -/
def derivedPullbackIdComparisonOf :
    𝟭 (Hom.ModuleDerived.{w} X) ⟶ h.modulePullbackDerived :=
  h.modulePullbackDerived.leftDerivedLift
    ((ToposHom.modulePullbackToDerived h).totalLeftDerivedCounit
      (Hom.moduleLocalization X) (Hom.ModuleQis X))
    (Hom.ModuleQis X) (𝟭 (Hom.ModuleDerived.{w} X)) (derivedPullbackIdCounitOf h hid)

/-- Component of `derivedPullbackIdComparisonOf` on an object of `D(O_X)`. -/
theorem derivedPullbackIdComparisonOf_app (K : Hom.ModuleDerived.{w} X) :
    (derivedPullbackIdComparisonOf h hid).app K =
      (h.modulePullbackDerived.leftDerivedLift
        ((ToposHom.modulePullbackToDerived h).totalLeftDerivedCounit
          (Hom.moduleLocalization X) (Hom.ModuleQis X))
        (Hom.ModuleQis X) (𝟭 (Hom.ModuleDerived.{w} X))
        (derivedPullbackIdCounitOf h hid)).app K :=
  sorry

/-- The identity comparison of derived module pullbacks is an isomorphism. -/
theorem derivedPullbackIdComparisonOf_isIso :
    IsIso (derivedPullbackIdComparisonOf h hid) :=
  sorry

end ToposHomIdComparisons

end CategoryTheory.SimplicialSites
