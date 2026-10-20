module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PullbackStalk
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition.ExactFirst

/-! # Derived pullback and geometric stalks -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open CategoryTheory.Functor.LeftDerived.Homotopy.Composition ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}}

/-- Underived pullback-stalk comparison, as a natural transformation. -/
noncomputable def pullbackStalkComparisonNatTrans {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (xbar' : GeometricPoint X') :
    (toSmallEtalePoint (xbar'.map g')).sheafModuleStalkFunctor (structureSheaf X) ⋙
        ModuleCat.extendScalars.{u, u, u} (etaleLocalRingMap g' xbar') ⟶
      Modules.pullback g' ⋙
        (toSmallEtalePoint xbar').sheafModuleStalkFunctor (structureSheaf X') :=
  { app := fun G ↦ Modules.pullbackStalkComparison g' G xbar'
    naturality := sorry }

set_option backward.isDefEq.respectTransparency false in
/-- The homotopy-to-derived counit of the stalk-then-extend-scalars route. -/
noncomputable def extensionStalkRouteCounit {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (xbar' : GeometricPoint X') :
    (DerivedCategory.Qh : HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X) ⋙
        (((toSmallEtalePoint (xbar'.map g')).sheafModuleStalkFunctor
            (structureSheaf X)).mapDerivedCategory ⋙
          ModuleCat.derivedExtensionOfScalars.{u, u, u} (etaleLocalRingMap g' xbar')) ⟶
      Functor.Homotopy.toDerived
        ((toSmallEtalePoint (xbar'.map g')).sheafModuleStalkFunctor (structureSheaf X) ⋙
          ModuleCat.extendScalars.{u, u, u} (etaleLocalRingMap g' xbar')) :=
  ExactFirst.counit
    (B := ModuleCat.{u} (etaleLocalRing X (xbar'.map g')))
    (C := ModuleCat.{u} (etaleLocalRing X' xbar'))
    ⟨(toSmallEtalePoint (xbar'.map g')).sheafModuleStalkFunctor (structureSheaf X),
      (toSmallEtalePoint (xbar'.map g')).sheafModuleStalk_exact (structureSheaf X)⟩
    (ModuleCat.extendScalars.{u, u, u} (etaleLocalRingMap g' xbar'))

/-- The homotopy-to-derived counit of the derived-pullback-then-stalk route. -/
noncomputable def pullbackStalkRouteCounit {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (xbar' : GeometricPoint X') :
    (DerivedCategory.Qh : HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X) ⋙
        (ModuleDerived.pullback g' ⋙
          ((toSmallEtalePoint xbar').sheafModuleStalkFunctor
            (structureSheaf X')).mapDerivedCategory) ⟶
      Functor.Homotopy.toDerived
        (Modules.pullback g' ⋙
          (toSmallEtalePoint xbar').sheafModuleStalkFunctor (structureSheaf X')) :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (ModuleDerived.pullbackCounit g') _ ≫
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _
            ((toSmallEtalePoint xbar').sheafModuleStalkFunctor
              (structureSheaf X')).mapDerivedCategoryFactorsh.hom ≫
          (toDerivedIso
              ((toSmallEtalePoint xbar').sheafModuleStalkFunctor (structureSheaf X'))
              (Modules.pullback g')
              (Modules.pullback g' ⋙
                (toSmallEtalePoint xbar').sheafModuleStalkFunctor (structureSheaf X'))
              (Iso.refl _)).inv

/-- The derived-pullback-then-stalk route is a left derived functor of its underived composite. -/
instance pullbackStalkRoute_isLeftDerived {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (xbar' : GeometricPoint X') :
    (ModuleDerived.pullback g' ⋙
        ((toSmallEtalePoint xbar').sheafModuleStalkFunctor
          (structureSheaf X')).mapDerivedCategory).IsLeftDerivedFunctor
      (pullbackStalkRouteCounit g' xbar')
      (HomotopyCategory.quasiIso (Modules X) (up ℤ)) := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Derived comparison `(L(g')^* E)_{x̄'} ⟵ E_{x̄} ⊗^L_{𝒪_{X, x̄}} 𝒪_{X', x̄'}`,
as a natural transformation. -/
noncomputable def pullbackStalkDerivedNatTrans {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (xbar' : GeometricPoint X') :
    ((toSmallEtalePoint (xbar'.map g')).sheafModuleStalkFunctor
          (structureSheaf X)).mapDerivedCategory ⋙
        ModuleCat.derivedExtensionOfScalars.{u, u, u} (etaleLocalRingMap g' xbar') ⟶
      ModuleDerived.pullback g' ⋙
        ((toSmallEtalePoint xbar').sheafModuleStalkFunctor
          (structureSheaf X')).mapDerivedCategory :=
  -- Local instance justification (defeq pin): pin the exact geometric stalk's additive
  -- structure before matching the composite underived target of the localization lift.
  let _ := (toSmallEtalePoint xbar').sheafModuleStalkFunctor_additive (structureSheaf X')
  -- Local instance justification (defeq pin): pin the displayed pullback's additive structure
  -- before elaborating the homotopy-level composite.
  let _ := Modules.instAdditive_pullback g'
  -- Local instance justification (defeq pin): the counit is indexed by the exact
  -- displayed composite, whose inferred category structures must match the lift.
  let _ := pullbackStalkRoute_isLeftDerived g' xbar'
  CategoryTheory.Functor.leftDerivedNatTrans
    (((toSmallEtalePoint (xbar'.map g')).sheafModuleStalkFunctor
        (structureSheaf X)).mapDerivedCategory ⋙
      ModuleCat.derivedExtensionOfScalars.{u, u, u} (etaleLocalRingMap g' xbar'))
    (ModuleDerived.pullback g' ⋙
      ((toSmallEtalePoint xbar').sheafModuleStalkFunctor
        (structureSheaf X')).mapDerivedCategory)
    (extensionStalkRouteCounit g' xbar') (pullbackStalkRouteCounit g' xbar')
    (HomotopyCategory.quasiIso (Modules X) (up ℤ))
    (Functor.whiskerRight
      (NatTrans.mapHomotopyCategory
        (F := (toSmallEtalePoint (xbar'.map g')).sheafModuleStalkFunctor
          (structureSheaf X) ⋙ ModuleCat.extendScalars.{u, u, u} (etaleLocalRingMap g' xbar'))
        (G := Modules.pullback g' ⋙
          (toSmallEtalePoint xbar').sheafModuleStalkFunctor (structureSheaf X'))
        (pullbackStalkComparisonNatTrans g' xbar') (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat (etaleLocalRing X' xbar')) (up ℤ) ⥤
          DerivedCategory (ModuleCat (etaleLocalRing X' xbar'))))

/-- Derived comparison
`(E_{x̄} ⊗^L_{𝒪_{X, x̄}} 𝒪_{X', x̄'}) ⟶ (L(g')^* E)_{x̄'}`. -/
noncomputable def pullbackStalkDerivedComparison {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (xbar' : GeometricPoint X') (E : ModuleDerived X) :
    (ModuleCat.derivedExtensionOfScalars.{u, u, u} (etaleLocalRingMap g' xbar')).obj
        (ModuleDerived.stalkDerived (xbar'.map g') E) ⟶
      ModuleDerived.stalkDerived xbar' ((ModuleDerived.pullback g').obj E) :=
  (pullbackStalkDerivedNatTrans g' xbar').app E

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived

end
