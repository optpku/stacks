/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Topology.KrullDimension.Equidimensional
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Equidimensional
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingModule

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.ModuleDerived.InternalHom
open AlgebraicGeometry.Scheme

noncomputable section

universe u

/- Example 48.22.2 (1): if `X` is an equidimensional scheme of finite type over a field
`k`, and `ωX` is a dualizing complex normalized relative to the affine image of `k[0]`,
then `H^{-dim(X)}(ωX)` is a dualizing module on `X`. -/
@[stacks 0AWJ] #check
  (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo.isDualizingModule_of_equidimensional :
    ∀ {k : Type u} [Field k]
      (X : AlgebraicGeometry.Scheme.FiniteTypeOver
        (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [TopologicalSpace.EquidimensionalSpace X.obj.left]
      [MonoidalCategory
        (AlgebraicGeometry.RingedSpace.ModuleDerived
          (AlgebraicGeometry.Spec (CommRingCat.of k)).toRingedSpace)]
      [MonoidalCategory
        (AlgebraicGeometry.RingedSpace.ModuleDerived (X.obj.left).toRingedSpace)]
      (HS : MonoidalClosed
        (AlgebraicGeometry.RingedSpace.ModuleDerived
          (AlgebraicGeometry.Spec (CommRingCat.of k)).toRingedSpace))
      (HX : MonoidalClosed
        (AlgebraicGeometry.RingedSpace.ModuleDerived (X.obj.left).toRingedSpace))
      (ωS : AlgebraicGeometry.RingedSpace.ModuleDerived
        (AlgebraicGeometry.Spec (CommRingCat.of k)).toRingedSpace)
      (hωS : ωS.IsDualizingComplex HS)
      (hωS_affine : IsIsomorphic ωS
        ((AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineTildeDerived k).obj
          (ModuleCat.single0 (ModuleCat.of k k))))
      (ωX : AlgebraicGeometry.RingedSpace.ModuleDerived (X.obj.left).toRingedSpace)
      (hωX : @AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo _ _ _
        X.obj.hom (AlgebraicGeometry.Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX)
      (d : ℕ) (h_dimension : topologicalKrullDim X.obj.left = d),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule ωX HX (-(d : ℤ))
        (AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologySheaf ωX (-(d : ℤ))))

/- Example 48.22.2 (2): for a finite-type separated scheme over `k`, the normalized
dualizing complex agrees with upper shriek of the base complex `k[0]`. -/
@[stacks 0AWJ] #check
  (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.omega_isIsomorphic_upperShriek :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [IsNoetherian S]
      [MonoidalCategory (AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace)]
      {H : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace)}
      {ωS : AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace}
      {hωS : ωS.IsDualizingComplex H}
      (D : AlgebraicGeometry.Scheme.NewUpperShriekAssignment S H ωS hωS)
      (E : AlgebraicGeometry.Scheme.UpperShriekAssignment S)
      (X : AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S),
      IsIsomorphic
        (D.omega
          (AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.toFiniteTypeOver X)).obj.obj
        ((E.map (AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.toBase X)).obj
          ((AlgebraicGeometry.Scheme.DerivedQCoh.coherentPlusInclusion S).obj
            (D.omega (AlgebraicGeometry.Scheme.FiniteTypeOver.base S)))).obj.obj)

/- Example 48.22.2 (3): for a proper scheme over a local Noetherian base, the canonical
quasicoherent right-adjoint value is the proper specialization of Example 48.22.1. -/
@[stacks 0AWI] #check
  (AlgebraicGeometry.Scheme.isDualizingModule_of_proper :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      {X : AlgebraicGeometry.Scheme.{u}}
      [hA₀ : HomotopyCategory.Koszul.TensorDescends (C := ModuleCat.{u} A)]
      [hA₁ : HomotopyCategory.KFlat.TensorDescends (C := ModuleCat.{u} A)]
      [hA₂ : DerivedCategory.KFlat.IsLocalization (C := ModuleCat.{u} A)]
      (HA : @MonoidalClosed (DerivedCategory (ModuleCat.{u} A)) _
        (DerivedCategory.KFlat.monoidalCategory (C := ModuleCat.{u} A)))
      [hX₀ : AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
        X.toRingedSpace]
      [hX₁ : AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.TensorDescends
        X.toRingedSpace]
      [hX₂ : AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.IsLocalization
        X.toRingedSpace]
      (HX : @MonoidalClosed
        (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace) _
        (AlgebraicGeometry.RingedSpace.ModuleDerived.monoidalCategory
          X.toRingedSpace))
      (ωA : DerivedCategory (ModuleCat.{u} A))
      (hωA : ωA.IsNormalizedDualizingComplex HA)
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) [IsProper f]
      (a : AlgebraicGeometry.Scheme.DerivedQCoh
        (AlgebraicGeometry.Spec (CommRingCat.of A)) ⥤ AlgebraicGeometry.Scheme.DerivedQCoh X)
      (aAdj : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (d : ℕ) (h_dimension : topologicalKrullDim X = d),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule
        ((a.obj ((AlgebraicGeometry.Scheme.DerivedQCoh.affineTilde
          (CommRingCat.of A)).obj ωA)).obj) HX (-(d : ℤ))
        (AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologySheaf
          ((a.obj ((AlgebraicGeometry.Scheme.DerivedQCoh.affineTilde
            (CommRingCat.of A)).obj ωA)).obj) (-(d : ℤ))))
