/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.LocalCohomology.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Gysin.BaseChange

variable {Z' X' S' Z X S : Scheme.{u}}

/-- The pullback on the source cohomology groups of the two Gysin maps, induced by the
outer square on relative `p`-forms. -/
noncomputable def sourceCohomology
    (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (g : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (k : S' ⟶ S)
    [IsClosedImmersion i'] [IsClosedImmersion i]
    [FinitePresentation i'] [FinitePresentation i]
    [Smooth f'] [Smooth f]
    [IsKoszulRegularImmersion i'] [IsKoszulRegularImmersion i]
    (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i')]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i)]
    (sqZX : IsPullback h i' i g) (sqXS : CommSq g f' f k) :
    (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
      AddCommGrpCat.{u}).obj
        (Arrow.mk (hodgeCohomologyMapOfSmoothOfKoszulRegular i f p q c)).left ⟶
      (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X'.toRingedSpace))
        AddCommGrpCat.{u}).obj
          (Arrow.mk (hodgeCohomologyMapOfSmoothOfKoszulRegular i' f' p q c)).left :=
  let M := (Scheme.Modules.toRingedSpace Z).obj
    (SheafOfModules.RingedSite.ExteriorPower.sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p)
  let M' := (Scheme.Modules.toRingedSpace Z').obj
    (SheafOfModules.RingedSite.ExteriorPower.sheaf Z'.𝒪 Ω[(i' ≫ f').toShHom] p)
  let K := (DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj M
  let K' := (DerivedCategory.singleFunctor Z'.toRingedSpace.Modules (c : ℤ)).obj M'
  let β := singlePullbackComparison h.toShHom M (c : ℤ) ≫
    (DerivedCategory.singleFunctor Z'.toRingedSpace.Modules (c : ℤ)).map
      ((Scheme.Modules.toRingedSpace Z').map
        (sourceFormMap h i' i g f' f k sqZX sqXS p))
  let α := (Scheme.Hom.derivedAdjunction h).homEquiv K K' β
  let topComparison := RingedSpace.Module.Derived.GlobalSections.restrictionHomologyIso i.toShHom
    ((RingedSpace.Module.Derived.GlobalSections.functor Z.toRingedSpace).obj K) (q + c : ℤ)
  let bottomComparison := RingedSpace.Module.Derived.GlobalSections.restrictionHomologyIso i'.toShHom
    ((RingedSpace.Module.Derived.GlobalSections.functor Z'.toRingedSpace).obj K') (q + c : ℤ)
  AddCommGrpCat.ofHom topComparison.inv.hom.toAddMonoidHom ≫
    RingedSpace.Module.Derived.GlobalSections.homologyMapOfPushforward h.toShHom α (q + c : ℤ) ≫
    AddCommGrpCat.ofHom bottomComparison.hom.hom.toAddMonoidHom

/-- The source pullback is the derived-global-sections map of the adjoint of the canonical
relative-form comparison, transported through scalar-restriction identifications. -/
theorem sourceCohomology_spec
    (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (g : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (k : S' ⟶ S)
    [IsClosedImmersion i'] [IsClosedImmersion i]
    [FinitePresentation i'] [FinitePresentation i]
    [Smooth f'] [Smooth f]
    [IsKoszulRegularImmersion i'] [IsKoszulRegularImmersion i]
    (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i')]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i)]
    (sqZX : IsPullback h i' i g) (sqXS : CommSq g f' f k) :
    sourceCohomology h i' i g f' f k c p q sqZX sqXS =
      let M := (Scheme.Modules.toRingedSpace Z).obj
        (SheafOfModules.RingedSite.ExteriorPower.sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p)
      let M' := (Scheme.Modules.toRingedSpace Z').obj
        (SheafOfModules.RingedSite.ExteriorPower.sheaf Z'.𝒪 Ω[(i' ≫ f').toShHom] p)
      let K := (DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj M
      let K' := (DerivedCategory.singleFunctor Z'.toRingedSpace.Modules (c : ℤ)).obj M'
      let β := singlePullbackComparison h.toShHom M (c : ℤ) ≫
        (DerivedCategory.singleFunctor Z'.toRingedSpace.Modules (c : ℤ)).map
          ((Scheme.Modules.toRingedSpace Z').map
            (sourceFormMap h i' i g f' f k sqZX sqXS p))
      let α :=
        (Scheme.Hom.derivedAdjunction h).homEquiv K K' β
      let topComparison :=
        RingedSpace.Module.Derived.GlobalSections.restrictionHomologyIso i.toShHom
          ((RingedSpace.Module.Derived.GlobalSections.functor Z.toRingedSpace).obj K)
            (q + c : ℤ)
      let bottomComparison :=
        RingedSpace.Module.Derived.GlobalSections.restrictionHomologyIso i'.toShHom
          ((RingedSpace.Module.Derived.GlobalSections.functor Z'.toRingedSpace).obj K')
            (q + c : ℤ)
      AddCommGrpCat.ofHom topComparison.inv.hom.toAddMonoidHom ≫
        RingedSpace.Module.Derived.GlobalSections.homologyMapOfPushforward h.toShHom α
          (q + c : ℤ) ≫
        AddCommGrpCat.ofHom bottomComparison.hom.hom.toAddMonoidHom := sorry

/-- The pullback on the target cohomology groups of the two Gysin maps, induced by the
degree-`p + c` relative-form comparison on the ambient square. -/
noncomputable def targetCohomology
    (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (g : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (k : S' ⟶ S)
    [IsClosedImmersion i'] [IsClosedImmersion i]
    [FinitePresentation i'] [FinitePresentation i]
    [Smooth f'] [Smooth f]
    [IsKoszulRegularImmersion i'] [IsKoszulRegularImmersion i]
    (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i')]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i)]
    (sqZX : IsPullback h i' i g) (sqXS : CommSq g f' f k) :
    (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
      AddCommGrpCat.{u}).obj
        (Arrow.mk (hodgeCohomologyMapOfSmoothOfKoszulRegular i f p q c)).right ⟶
      (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X'.toRingedSpace))
        AddCommGrpCat.{u}).obj
          (Arrow.mk (hodgeCohomologyMapOfSmoothOfKoszulRegular i' f' p q c)).right :=
  let F := relativeFormQCoh f (p + c)
  let K := (ModuleCech.moduleToDerived X).obj ((Scheme.QCoh.inclusion X).obj F)
  let F' := relativeFormQCoh f' (p + c)
  let K' := (ModuleCech.moduleToDerived X').obj ((Scheme.QCoh.inclusion X').obj F')
  let β := Scheme.Hom.LocalCohomology.BaseChange.coefficientComparison g F ≫
    (ModuleCech.moduleToDerived X').map
      ((Scheme.QCoh.inclusion X').map (formMap sqXS (p + c)))
  let α := (Scheme.Hom.derivedAdjunction g).homEquiv K K' β
  RingedSpace.Module.Derived.GlobalSections.homologyMapOfPushforward g.toShHom α (q + c : ℤ)

/-- The target pullback is the derived-global-sections map of the adjoint of the ambient
relative-form comparison in degree `p + c`. -/
theorem targetCohomology_spec
    (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (g : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (k : S' ⟶ S)
    [IsClosedImmersion i'] [IsClosedImmersion i]
    [FinitePresentation i'] [FinitePresentation i]
    [Smooth f'] [Smooth f]
    [IsKoszulRegularImmersion i'] [IsKoszulRegularImmersion i]
    (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i')]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i)]
    (sqZX : IsPullback h i' i g) (sqXS : CommSq g f' f k) :
    targetCohomology h i' i g f' f k c p q sqZX sqXS =
      let F := relativeFormQCoh f (p + c)
      let K := (ModuleCech.moduleToDerived X).obj ((Scheme.QCoh.inclusion X).obj F)
      let F' := relativeFormQCoh f' (p + c)
      let K' := (ModuleCech.moduleToDerived X').obj ((Scheme.QCoh.inclusion X').obj F')
      let β := Scheme.Hom.LocalCohomology.BaseChange.coefficientComparison g F ≫
        (ModuleCech.moduleToDerived X').map
          ((Scheme.QCoh.inclusion X').map (formMap sqXS (p + c)))
      let α :=
        (Scheme.Hom.derivedAdjunction g).homEquiv K K' β
      RingedSpace.Module.Derived.GlobalSections.homologyMapOfPushforward g.toShHom α
        (q + c : ℤ) := sorry

end AlgebraicGeometry.Scheme.DeRham.Gysin.BaseChange

namespace AlgebraicGeometry.Scheme.DeRham.Gysin

variable {Z' X' S' Z X S : Scheme.{u}}

/-- Base change commutes with the cohomological Gysin morphism for smooth ambient maps and
Koszul-regular finitely presented closed immersions. -/
theorem hodgeCohomologyMap_baseChange
    (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (g : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (k : S' ⟶ S)
    [IsClosedImmersion i'] [IsClosedImmersion i]
    [FinitePresentation i'] [FinitePresentation i]
    [Smooth f'] [Smooth f]
    [IsKoszulRegularImmersion i'] [IsKoszulRegularImmersion i]
    (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i')]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i)]
    (sqZX : IsPullback h i' i g) (sqXS : CommSq g f' f k)
    [IsIso (Conormal.map sqZX.toCommSq)] :
    CommSq
      ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
        AddCommGrpCat.{u}).map
          (hodgeCohomologyMapOfSmoothOfKoszulRegular i f p q c))
      (BaseChange.sourceCohomology h i' i g f' f k c p q sqZX sqXS)
      (BaseChange.targetCohomology h i' i g f' f k c p q sqZX sqXS)
      ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing X'.toRingedSpace))
        AddCommGrpCat.{u}).map
          (hodgeCohomologyMapOfSmoothOfKoszulRegular i' f' p q c)) := sorry

end AlgebraicGeometry.Scheme.DeRham.Gysin

end
