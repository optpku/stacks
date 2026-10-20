/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution.Dualizing
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.AffineComparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex
open scoped AlgebraicGeometry

universe u

/- Lemma 58.28.1 (1): if a two-dimensional Noetherian normal local Nagata domain with a
dualizing module has a resolution whose dualizing module is the sheaf associated to an effective
Cartier divisor supported on the exceptional fibre, then it defines a rational singularity. -/
@[stacks 0EA2] #check (IsRationalSingularity.ofExceptionalDualizingModule :
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
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
    (hωX_iso : IsIsomorphic ωX E.associatedSheaf),
    IsRationalSingularity A)

/- Lemma 58.28.1 (2): under the same hypotheses, if the resolution is minimal, then the
effective Cartier divisor representing its dualizing module is zero. -/
@[stacks 0EA2] #check (IsRationalSingularity.effectiveDivisor_eq_zero_of_minimal :
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
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
    (h_minimal : AlgebraicGeometry.IsMinimalResolution f),
    E = (⊤ : X.IdealSheafData))

/- A resolution minimality predicate is characterized by its factorization property. -/
#check (AlgebraicGeometry.IsMinimalResolution :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian Y] [IsIntegral Y] [IsResolution f], Prop)
#check (AlgebraicGeometry.isMinimalResolution_iff :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian Y] [IsIntegral Y] [IsResolution f],
    AlgebraicGeometry.IsMinimalResolution f ↔
      ∀ (Z : Scheme.{u}) (g : Z ⟶ Y) [IsResolution g],
        ∃ u : Z ⟶ X, u ≫ f = g)
