/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Finite
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory
open DerivedCategory.Plus
open CohomologyIn
open SheafOfModules.RingedSite
open LocallyRingedSpace.Hom
open RingedSpace.ModuleDerived.KFlat
open Scheme
open Scheme.Hom

noncomputable section

universe u

/- Remark 48.20.12 -/
@[stacks 0AX4] #check (AlgebraicGeometry.Scheme.DerivedQCoh.normalizedDualizing_affinePushforward_isIsomorphic_internalHom : ∀ {S : Scheme.{u}} [IsNoetherian S] {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y) [IsFinite f.hom.left] [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)] (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)) [MonoidalCategory (RingedSpace.ModuleDerived X.obj.left.toRingedSpace)] (HX : MonoidalClosed (RingedSpace.ModuleDerived X.obj.left.toRingedSpace)) [MonoidalCategory (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace)] (HY : MonoidalClosed (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace)) (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS) (ωX : Scheme.DerivedQCoh.Plus X.obj.left) (ωY : Scheme.DerivedQCoh.Plus Y.obj.left) (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj.obj) (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj.obj), IsIsomorphic ((Scheme.DerivedQCoh.affinePushforwardToPushforwardStructurePlus f.hom.left).obj ωX) ((Scheme.DerivedQCoh.derivedInternalHomPlus f.hom.left).obj ωY))

/- Remark 48.20.12 (2) -/
@[stacks 0AX4] #check (AlgebraicGeometry.Scheme.DerivedQCoh.normalizedDualizingTrace_eq_evaluationAtOne : ∀ {S : Scheme.{u}} [IsNoetherian S] {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y) [IsFinite f.hom.left] [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)] [HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)] [HomotopyTensorDescends (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))] [TensorDescends (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))] [IsLocalization (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))] [HomotopyTensorDescends (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))] [TensorDescends (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))] [IsLocalization (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))] [HX : MonoidalClosed (RingedSpace.ModuleDerived (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left)))] [HY : MonoidalClosed (RingedSpace.ModuleDerived (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left)))] (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS) (ωX : Scheme.DerivedQCoh.Plus X.obj.left) (ωY : Scheme.DerivedQCoh.Plus Y.obj.left) (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj.obj) (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj.obj), ∃ (e : ((DerivedCategory.cohomologyIn (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace)).ι).obj ((Scheme.DerivedQCoh.pushforwardCohomologyIn f.hom.left).obj ((toUnbounded (RingedSpace.quasiCoherentModuleProperty X.obj.left.toRingedSpace)).obj ωX)) ≅ (DerivedCoextension.restriction (RingedSpace.Hom.commRingSheafPushforwardMap f.hom.left.toShHom)).obj ((DerivedCoextension.functor (RingedSpace.Hom.commRingSheafPushforwardMap f.hom.left.toShHom)).obj ((ambient (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace)).obj ωY))), e.hom ≫ Scheme.DerivedQCoh.structureSheafInducedMap f.hom.left ωY = ((DerivedCategory.cohomologyIn (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace)).ι).map (Scheme.DerivedQCoh.normalizedDualizingTrace f ωS hωS ((toUnbounded (RingedSpace.quasiCoherentModuleProperty X.obj.left.toRingedSpace)).obj ωX) ((toUnbounded (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace)).obj ωY) hX hY))

