/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RationalSingularity.DualizingTrace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace IsRationalSingularity

/- Lemma 54.9.6 -/
@[stacks 0BBU] #check
  (IsRationalSingularity.dualizingTrace_isIso :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (.of A))
      [IsModification f]
    (h_normal : X.isNormal) (h_locallyNoetherian : IsLocallyNoetherian X)
    (ωX : X.Modules) (hωX : @AlgebraicGeometry.Scheme.IsDualizingModule X h_locallyNoetherian ωX)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ωA : ModuleCat.{u} A) (hωA : ModuleCat.IsDualizingModule ωA)
    [MonoidalCategory
      (RingedSpace.ModuleDerived (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace)]
    (HS : MonoidalClosed
      (RingedSpace.ModuleDerived (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace))
    (ωS : RingedSpace.ModuleDerived (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : ωS.IsDualizingComplex HS)
    (hωS_affine : IsIsomorphic ωS
      ((AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul.affineDerivedTilde A).obj
        ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (h_relative : AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo f HS HX
      ωS hωS (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (a : RingedSpace.ModuleDerived (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace ⥤
      RingedSpace.ModuleDerived X.toRingedSpace)
    (aAdjunction : RingedSpace.moduleDerivedPushforward f.toShHom ⊣ a)
    (e : a.obj ωS ≅ (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (sourceComparison : AlgebraicGeometry.Scheme.Hom.globalSectionsMod f ωX ≅
      (IsRationalSingularity.dualizingGlobalSectionsFunctor A).obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)))
    (targetComparison : (IsRationalSingularity.dualizingGlobalSectionsFunctor A).obj ωS ≅ ωA),
    IsIso (IsRationalSingularity.dualizingTrace A f h_normal h_locallyNoetherian ωX hωX HA ωA hωA
      HS ωS hωS hωS_affine HX h_relative a aAdjunction e sourceComparison targetComparison))

#check (IsRationalSingularity.canonicalDualizingPullbackMap :
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (.of A))
      [IsModification f]
    (h_normal : X.isNormal) (h_locallyNoetherian : IsLocallyNoetherian X)
    (ωX : X.Modules) (hωX : @AlgebraicGeometry.Scheme.IsDualizingModule X h_locallyNoetherian ωX)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ωA : ModuleCat.{u} A) (hωA : ModuleCat.IsDualizingModule ωA)
    [MonoidalCategory
      (RingedSpace.ModuleDerived (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace)]
    (HS : MonoidalClosed
      (RingedSpace.ModuleDerived (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace))
    (ωS : RingedSpace.ModuleDerived (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : ωS.IsDualizingComplex HS)
    (hωS_affine : IsIsomorphic ωS
      ((AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul.affineDerivedTilde A).obj
        ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (h_relative : AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo f HS HX
      ωS hωS (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (a : RingedSpace.ModuleDerived (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace ⥤
      RingedSpace.ModuleDerived X.toRingedSpace)
    (aAdjunction : RingedSpace.moduleDerivedPushforward f.toShHom ⊣ a)
    (e : a.obj ωS ≅ (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (sourceComparison : AlgebraicGeometry.Scheme.Hom.globalSectionsMod f ωX ≅
      (IsRationalSingularity.dualizingGlobalSectionsFunctor A).obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)))
    (targetComparison : (IsRationalSingularity.dualizingGlobalSectionsFunctor A).obj ωS ≅ ωA),
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.tilde ωA) ⟶ ωX)

end IsRationalSingularity
