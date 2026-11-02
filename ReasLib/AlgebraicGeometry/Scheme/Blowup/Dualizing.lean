/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.LocallySurjective
public import ReasLib.AlgebraicGeometry.RationalSingularity.DualizingTrace
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExceptionalFiber
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.TwistingSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex
open AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex
open RingedSpace.Module.Derived

noncomputable section

universe u

open IsRationalSingularity

namespace AlgebraicGeometry.IsBlowup

/-- For a nonregular rational surface blowup with compatible dualizing data, the dualizing
module of the exceptional curve is the restricted dualizing module twisted by `-1`. -/
theorem exceptionalDualizingModule_spec
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    (h_notRegular : ¬ IsRegularLocalRing A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (h_normal : X.isNormal) (h_locallyNoetherian : IsLocallyNoetherian X)
    (ωX : X.Modules) (hωX : @Scheme.IsDualizingModule X h_locallyNoetherian ωX)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ωA : ModuleCat.{u} A) (hωA : ModuleCat.IsDualizingModule ωA)
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)]
    (HS : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : ωS.IsDualizingComplex HS)
    (hωS_affine : IsIsomorphic ωS
      ((affineDerivedTilde A).obj ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (h_relative : RelativeTo f HS HX ωS hωS
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)) :
    IsIsomorphic
      (@curveDualizingModule _ _ _
        (f.fiberToSpecResidueField (IsLocalRing.closedPoint A))
        (instIsProperExceptionalFiber A f))
      ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint A))).obj ωX ⊗
        (Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint A))).obj
          (twistingSheaf (IsLocalRing.maximalIdeal A) f (-1))) := sorry

/-- For the same blowup data, the first cohomology of every nonnegative twist of the
dualizing module vanishes. -/
theorem dualizingTwist_firstCohomology_isZero
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    (h_notRegular : ¬ IsRegularLocalRing A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (h_normal : X.isNormal) (h_locallyNoetherian : IsLocallyNoetherian X)
    (ωX : X.Modules) (hωX : @Scheme.IsDualizingModule X h_locallyNoetherian ωX)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ωA : ModuleCat.{u} A) (hωA : ModuleCat.IsDualizingModule ωA)
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)]
    (HS : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : ωS.IsDualizingComplex HS)
    (hωS_affine : IsIsomorphic ωS
      ((affineDerivedTilde A).obj ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (h_relative : RelativeTo f HS HX ωS hωS
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (n : ℕ) :
    IsZero (Scheme.Modules.cohomology
      (ωX ⊗ twistingSheaf (IsLocalRing.maximalIdeal A) f (n : ℤ)) 1) := sorry

/-- For a nonregular rational surface blowup with compatible dualizing data, the canonical
pullback map from the base dualizing module is locally surjective. -/
theorem canonicalDualizingPullbackMap_isLocallySurjective
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    [h_notRegular : Fact (¬ IsRegularLocalRing A)]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (h_normal : X.isNormal) (h_locallyNoetherian : IsLocallyNoetherian X)
    (ωX : X.Modules) (hωX : @Scheme.IsDualizingModule X h_locallyNoetherian ωX)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ωA : ModuleCat.{u} A) (hωA : ModuleCat.IsDualizingModule ωA)
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)]
    (HS : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : ωS.IsDualizingComplex HS)
    (hωS_affine : IsIsomorphic ωS
      ((affineDerivedTilde A).obj ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (h_relative : RelativeTo f HS HX ωS hωS
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (a : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace ⥤
      RingedSpace.ModuleDerived X.toRingedSpace)
    (aAdjunction : RingedSpace.moduleDerivedPushforward f.toShHom ⊣ a)
    (e : a.obj ωS ≅ (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (sourceComparison : Scheme.Hom.globalSectionsMod f ωX ≅
      (dualizingGlobalSectionsFunctor A).obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)))
    (targetComparison : (dualizingGlobalSectionsFunctor A).obj ωS ≅ ωA)
    (traceInverse : ωA ⟶ Scheme.Hom.globalSectionsMod f ωX)
    (traceInverse_hom_id : traceInverse ≫
      (dualizingTrace A f h_normal h_locallyNoetherian ωX hωX HA ωA hωA HS
        ωS hωS hωS_affine HX h_relative a aAdjunction e sourceComparison targetComparison) = 𝟙 ωA)
    (hom_traceInverse_id :
      (dualizingTrace A f h_normal h_locallyNoetherian ωX hωX HA ωA hωA HS
        ωS hωS hωS_affine HX h_relative a aAdjunction e sourceComparison targetComparison) ≫ traceInverse =
        𝟙 (Scheme.Hom.globalSectionsMod f ωX)) :
    Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (canonicalDualizingPullbackMap A f h_normal h_locallyNoetherian ωX hωX HA ωA hωA HS
        ωS hωS hωS_affine HX h_relative a aAdjunction e sourceComparison targetComparison
        traceInverse traceInverse_hom_id hom_traceInverse_id)) := sorry

end AlgebraicGeometry.IsBlowup
