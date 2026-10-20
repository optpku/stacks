/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TorDimension.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BaseChange.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.ToUnbounded
public import ReasLib.RingTheory.RingHom.Perfect.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory DerivedCategory.Plus.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

open BaseChange

/-- For a Tor-independent cartesian square of quasi-compact, quasi-separated schemes
with affine bases, proper flat finitely presented vertical map, the right-adjoint
base-change map is an isomorphism on every unbounded quasi-coherent complex. -/
theorem mapOfRight_app_isIso_of_flat
    {X' X Y' Y : Scheme.{u}}
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [IsAffine Y'] [IsAffine Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    (sq : IsPullback g' f' f g)
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (dualBaseChangeIso :
      a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
    (h_dualBaseChange : dualBaseChangeIso.hom =
      rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
    (K : DerivedQCoh Y) :
    IsIso
      ((DerivedBaseChange.mapOfRight
        (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction g')
        dualBaseChangeIso.inv).app K) := sorry

/-- For a Tor-independent cartesian square of quasi-compact, quasi-separated schemes
with affine bases, Noetherian target, and proper perfect vertical map, the right-adjoint
base-change map is an isomorphism on every unbounded quasi-coherent complex. -/
theorem mapOfRight_app_isIso_of_perfect
    {X' X Y' Y : Scheme.{u}}
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [IsAffine Y'] [IsAffine Y] [IsNoetherian Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsProper f] [LocallyOfType RingHom.IsPerfectRingMap f]
    (sq : IsPullback g' f' f g)
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (dualBaseChangeIso :
      a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
    (h_dualBaseChange : dualBaseChangeIso.hom =
      rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
    (K : DerivedQCoh Y) :
    IsIso
      ((DerivedBaseChange.mapOfRight
        (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction g')
        dualBaseChangeIso.inv).app K) := sorry

/-- For a Tor-independent cartesian square of quasi-compact, quasi-separated schemes
with affine bases, Noetherian target, proper vertical map, and finite-Tor-dimension
horizontal map, the right-adjoint base-change map is an isomorphism on every
bounded-below quasi-coherent complex after passage to the unbounded category. -/
theorem mapOfRight_app_isIso_of_finiteTorDimension
    {X' X Y' Y : Scheme.{u}}
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [IsAffine Y'] [IsAffine Y] [IsNoetherian Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsProper f] [RingedSpace.Hom.HasFiniteTorDimension g.toShHom]
    (sq : IsPullback g' f' f g)
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (dualBaseChangeIso :
      a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
    (h_dualBaseChange : dualBaseChangeIso.hom =
      rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
    (K : DerivedQCoh.Plus Y) :
    IsIso
      ((DerivedBaseChange.mapOfRight
        (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction g')
        dualBaseChangeIso.inv).app
          ((toUnbounded Y.toRingedSpace.quasiCoherentModuleProperty).obj K)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
