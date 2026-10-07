module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Dualizing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex
open AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex
open RingedSpace.Module.Derived

universe u

/- Lemma 54.9.7 (1): in Situation 54.9.1, the canonical curve dualizing module
of the exceptional divisor is isomorphic to `ωX|_E ⊗ 𝒪_E(-1)`. -/
@[stacks 0B64] #check
  (AlgebraicGeometry.IsBlowup.exceptionalDualizingModule_spec :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
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
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)),
    IsIsomorphic
      (@curveDualizingModule _ _ _
        (f.fiberToSpecResidueField (IsLocalRing.closedPoint A))
        (AlgebraicGeometry.IsBlowup.instIsProperExceptionalFiber A f))
      ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint A))).obj ωX ⊗
        (Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint A))).obj
          (AlgebraicGeometry.IsBlowup.twistingSheaf
            (IsLocalRing.maximalIdeal A) f (-1))))

/- Lemma 54.9.7 (2): for every `n ≥ 0`, the first cohomology of `ωX(n)` vanishes. -/
@[stacks 0B64] #check
  (AlgebraicGeometry.IsBlowup.dualizingTwist_firstCohomology_isZero :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
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
    (n : ℕ),
    IsZero (Scheme.Modules.cohomology
      (ωX ⊗ AlgebraicGeometry.IsBlowup.twistingSheaf
        (IsLocalRing.maximalIdeal A) f (n : ℤ)) 1))

/- Lemma 54.9.7 (3): the canonical pullback map of Lemma 54.9.6 is locally surjective. -/
@[stacks 0B64] #check
  (AlgebraicGeometry.IsBlowup.canonicalDualizingPullbackMap_isLocallySurjective :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
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
      (IsRationalSingularity.dualizingGlobalSectionsFunctor A).obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)))
    (targetComparison : (IsRationalSingularity.dualizingGlobalSectionsFunctor A).obj ωS ≅ ωA),
    Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (IsRationalSingularity.canonicalDualizingPullbackMap A f h_normal
        h_locallyNoetherian ωX hωX HA ωA hωA HS ωS hωS hωS_affine HX h_relative a
        aAdjunction e sourceComparison targetComparison)))
