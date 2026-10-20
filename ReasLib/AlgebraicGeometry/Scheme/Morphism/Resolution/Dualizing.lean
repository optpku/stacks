/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DualizingModule
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.AffineComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Dualizing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution.Minimal
public import ReasLib.RingTheory.Normal.Local
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.Normal.RationalSingularity

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex
open scoped AlgebraicGeometry

universe u

namespace IsRationalSingularity

/-- A dualizing module represented by an effective exceptional Cartier divisor on a resolution
of a two-dimensional normal local Nagata domain implies a rational singularity. -/
theorem ofExceptionalDualizingModule
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsNormalRing A] [NagataRing A] (h_dimension : ringKrullDim A = 2)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsResolution f]
    (hX_noetherian : IsLocallyNoetherian X) (hX_normal : X.isNormal)
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
      ((AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineTildeDerived A).obj
        ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωX : X.Modules)
    (hωX : @Scheme.IsDualizingModule X hX_noetherian ωX)
    (h_relative : RelativeTo f HS HX ωS hωS
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (E : X.IdealSheafData) [IsEffectiveCartierDivisor E.subschemeι]
    (hE_support : (E.support : Set X) ⊆
      Set.range (f.fiberι (IsLocalRing.closedPoint A)))
    (hωX_iso : IsIsomorphic ωX E.associatedSheaf) :
    IsRationalSingularity A := sorry

/-- On a minimal resolution, an effective exceptional Cartier divisor representing the dualizing
module is the zero divisor. -/
theorem effectiveDivisor_eq_zero_of_minimal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsNormalRing A] [NagataRing A] (h_dimension : ringKrullDim A = 2)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsResolution f]
    (hX_noetherian : IsLocallyNoetherian X) (hX_normal : X.isNormal)
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
      ((AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineTildeDerived A).obj
        ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωX : X.Modules)
    (hωX : @Scheme.IsDualizingModule X hX_noetherian ωX)
    (h_relative : RelativeTo f HS HX ωS hωS
      (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
    (E : X.IdealSheafData) [IsEffectiveCartierDivisor E.subschemeι]
    (hE_support : (E.support : Set X) ⊆
      Set.range (f.fiberι (IsLocalRing.closedPoint A)))
    (hωX_iso : IsIsomorphic ωX E.associatedSheaf)
    (h_minimal : AlgebraicGeometry.IsMinimalResolution f) :
    E = (⊤ : X.IdealSheafData) := sorry

end IsRationalSingularity
