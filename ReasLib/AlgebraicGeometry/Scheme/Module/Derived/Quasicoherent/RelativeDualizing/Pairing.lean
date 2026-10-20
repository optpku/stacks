/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.SheafyTrace.Finiteness
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Pushforward.FlatCoefficients
public import ReasLib.CategoryTheory.Monoidal.Closed.AdjunctionComparison

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Currying the relative cup product followed by a pairing and the relative dualizing
trace agrees with pushing forward the curried pairing and applying the sheafy trace map. -/
theorem relativeCupProductTrace_curry
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace]
    [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K M : DerivedQCoh X)
    (pairing : K.obj ⊗ M.obj ⟶ (relativeDualizingComplex f a aAdjunction).obj) :
    braidedHomEquiv
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj K.obj)
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj M.obj)
        (structureSheaf Y).obj
        (@RingedSite.Hom.modulePushforwardDerived.cupProduct _ _
            (RingedSpace.opensRingedSiteHom f.toShHom) _ _ _ _ _ _ _ _
            (Functor.Monoidal.toOplaxMonoidal
              (F := RingedSpace.modulePullbackDerived f.toShHom)) K.obj M.obj ≫
          (RingedSpace.moduleDerivedPushforward f.toShHom).map pairing ≫
          (pushforwardCohomologyIn.inclusionIso f).inv.app
            (relativeDualizingComplex f a aAdjunction) ≫
          (inclusion Y).map (relativeDualizingTrace f a aAdjunction)) =
      (RingedSpace.moduleDerivedPushforward f.toShHom).map
          (braidedHomEquiv K.obj M.obj
            (relativeDualizingComplex f a aAdjunction).obj pairing) ≫
        uncoheratedSheafyTraceMap f a aAdjunction M (structureSheaf Y) := sorry

/-- A relative pairing with pseudo-coherent second factor whose curry is invertible
induces an invertible curried pairing after derived pushforward and the dualizing trace. -/
theorem relativeCupProductTraceCurryIsIso
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace]
    [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K M : DerivedQCoh X)
    (pairing : K.obj ⊗ M.obj ⟶ (relativeDualizingComplex f a aAdjunction).obj)
    [Fact (RingedSpace.ModuleDerived.IsPseudoCoherent M.obj)]
    [IsIso (braidedHomEquiv K.obj M.obj
      (relativeDualizingComplex f a aAdjunction).obj pairing)] :
    IsIso
      (braidedHomEquiv
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj K.obj)
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj M.obj)
        (structureSheaf Y).obj
        (@RingedSite.Hom.modulePushforwardDerived.cupProduct _ _
            (RingedSpace.opensRingedSiteHom f.toShHom) _ _ _ _ _ _ _ _
            (Functor.Monoidal.toOplaxMonoidal
              (F := RingedSpace.modulePullbackDerived f.toShHom)) K.obj M.obj ≫
          (RingedSpace.moduleDerivedPushforward f.toShHom).map pairing ≫
          (pushforwardCohomologyIn.inclusionIso f).inv.app
            (relativeDualizingComplex f a aAdjunction) ≫
          (inclusion Y).map (relativeDualizingTrace f a aAdjunction))) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
