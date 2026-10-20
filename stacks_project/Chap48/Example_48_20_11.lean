/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Trace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.MonoidalClosed
open LocallyRingedSpace.Hom
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction
open Scheme
open Scheme.Hom

noncomputable section

universe u

/- Example 48.20.11 -/
@[stacks 0B6X] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.normalizedDualizingTrace :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y) [IsProper f.hom.left]
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      [HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]
      [HomotopyTensorDescends
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
      [TensorDescends
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
      [IsLocalization
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
      [HomotopyTensorDescends
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
      [TensorDescends
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
      [IsLocalization
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
      [HX : MonoidalClosed (RingedSpace.ModuleDerived
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left)))]
      [HY : MonoidalClosed (RingedSpace.ModuleDerived
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left)))]
      (ωS : RingedSpace.ModuleDerived S.toRingedSpace)
      (hωS : ωS.IsDualizingComplex HS)
      (ωX : DerivedQCoh X.obj.left) (ωY : DerivedQCoh Y.obj.left)
      (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
        (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj)
      (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
        (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj),
      (DerivedQCoh.pushforwardCohomologyIn f.hom.left).obj ωX ⟶ ωY)

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.normalizedDualizingHomEquiv :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y) [IsProper f.hom.left]
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      [HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]
      [HomotopyTensorDescends
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
      [TensorDescends
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
      [IsLocalization
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
      [HomotopyTensorDescends
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
      [TensorDescends
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
      [IsLocalization
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
      [HX : MonoidalClosed (RingedSpace.ModuleDerived
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left)))]
      [HY : MonoidalClosed (RingedSpace.ModuleDerived
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left)))]
      (ωS : RingedSpace.ModuleDerived S.toRingedSpace)
      (hωS : ωS.IsDualizingComplex HS)
      (ωX : DerivedQCoh X.obj.left) (ωY : DerivedQCoh Y.obj.left)
      (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
        (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj)
      (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
        (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj)
      (L : DerivedQCoh X.obj.left),
      (L ⟶ ωX) ≃
        ((DerivedQCoh.pushforwardCohomologyIn f.hom.left).obj L ⟶ ωY))

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.normalizedDualizingSheafyTraceMapIsIso :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y) [IsProper f.hom.left]
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      [HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]
      [HomotopyTensorDescends
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
      [TensorDescends
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
      [IsLocalization
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
      [HomotopyTensorDescends
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
      [TensorDescends
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
      [IsLocalization
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
      [HX : MonoidalClosed (RingedSpace.ModuleDerived
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left)))]
      [HY : MonoidalClosed (RingedSpace.ModuleDerived
        (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left)))]
      (ωS : RingedSpace.ModuleDerived S.toRingedSpace)
      (hωS : ωS.IsDualizingComplex HS)
      (ωX : DerivedQCoh X.obj.left) (ωY : DerivedQCoh Y.obj.left)
      [HasPair (RingedSpace.opensRingedSiteHom (toShHom (toLRSHom f.hom.left)))]
      [Functor.Monoidal
        (RingedSpace.modulePullbackDerived (toShHom (toLRSHom f.hom.left)))]
      (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
        (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj)
      (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
        (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj)
      (L : DerivedQCoh X.obj.left),
      IsIso (AlgebraicGeometry.Scheme.DerivedQCoh.normalizedDualizingSheafyTraceMap
        f ωS hωS ωX ωY hX hY L))
