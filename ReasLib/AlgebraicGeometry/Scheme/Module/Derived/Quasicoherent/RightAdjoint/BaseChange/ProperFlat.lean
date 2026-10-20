/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.BaseChange.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.BaseChange.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.OpenRestriction

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Proper flat morphisms of finite presentation satisfy derived quasicoherent right-adjoint
base change along every morphism between quasi-compact quasi-separated schemes. -/
theorem mapOfRight_app_isIso_of_proper_flat
    {X Y' Y : Scheme.{u}}
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (a' : DerivedQCoh Y' ⥤ DerivedQCoh (CategoryTheory.Limits.pullback f g))
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn (CategoryTheory.Limits.pullback.snd f g) ⊣ a')
    (K : DerivedQCoh Y) :
    IsIso
      ((DerivedBaseChange.mapOfRight
        (pullbackPushforwardAdjunction g)
        (pullbackPushforwardAdjunction (CategoryTheory.Limits.pullback.fst f g))
        (rightMateIsoOfFlatLeft f g a a' fAdj f'Adj).inv).app K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
