/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver
public import stacks_project.Chap75.Lemma_75_20_7_BaseChange

/-!
# Perfect derived pushforward of bounded coherent complexes of finite Tor dimension

Along a locally of finite type quasi-separated morphism of algebraic spaces with
Noetherian target, derived pushforward of a bounded coherent complex with
cohomology support proper over the target and finite relative Tor dimension is
perfect.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure TopologicalSpace

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Finite Tor dimension as an object of `D(f⁻¹𝒪_Y)` means the existence of a
finite Tor-amplitude interval over `f`. -/
abbrev HasFiniteTorDimensionOver (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived
        (SmallEtaleModuleGlueing.restrictFunctor_hom sq.left ⋙ Modules.restrictToScheme sq.left.left ⋙
          Scheme.Modules.toRingedSpace sq.left.left.left)).HasLeftDerivedFunctor (ModuleQis X)]
    [∀ sq : EtaleSquare f, DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom))] (E : ModuleDerived X) : Prop :=
  ∃ a b : ℤ, HasTorAmplitudeInOver f E a b

/-- Finite Tor dimension over `f` is equivalent to the existence of a finite
relative Tor-amplitude interval. -/
theorem hasFiniteTorDimensionOver_iff (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived
        (SmallEtaleModuleGlueing.restrictFunctor_hom sq.left ⋙ Modules.restrictToScheme sq.left.left ⋙
          Scheme.Modules.toRingedSpace sq.left.left.left)).HasLeftDerivedFunctor (ModuleQis X)]
    [∀ sq : EtaleSquare f, DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom))] (E : ModuleDerived X) :
    HasFiniteTorDimensionOver f E ↔
      ∃ a b : ℤ, HasTorAmplitudeInOver f E a b := sorry

/-- Lemma 75.22.1: let `S` be a scheme and let `Y` be a Noetherian algebraic space
over `S`. Let `f : X ⟶ Y` be a morphism of algebraic spaces which is locally of
finite type and quasi-separated. If `E` is an object of `D(𝒪_X)` which lies in
`D^b_Coh(𝒪_X)`, the support of `H^i(E)` is proper over `Y` for all `i`, and `E`
has finite Tor dimension as an object of `D(f⁻¹𝒪_Y)`, then
`(Modules.pushforwardDerived f).obj E` is a perfect object of `D(𝒪_Y)`. -/
@[stacks 08IS]
theorem pushforwardDerived_isPerfect_of_finiteTorDimension
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived
        (SmallEtaleModuleGlueing.restrictFunctor_hom sq.left ⋙ Modules.restrictToScheme sq.left.left ⋙
          Scheme.Modules.toRingedSpace sq.left.left.left)).HasLeftDerivedFunctor (ModuleQis X)]
    [∀ sq : EtaleSquare f, DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom))] [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian Y]
    (E : ModuleDerived X)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) E)
    (hE_bounded : (t.bounded : ObjectProperty (ModuleDerived X)) E)
    (hE_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Closeds.closure
        (Modules.moduleSupport
          ((DerivedCategory.homologyFunctor (Modules X) i).obj E))))
    (hE_tor : HasFiniteTorDimensionOver f E) :
    IsPerfect ((Modules.pushforwardDerived f).obj E) := sorry

/-- Derived pushforward of a bounded coherent complex with cohomology support
proper over a Noetherian target, and with a fixed relative Tor-amplitude
interval, is perfect. -/
theorem pushforwardDerived_isPerfect_of_hasTorAmplitudeInOver
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived
        (SmallEtaleModuleGlueing.restrictFunctor_hom sq.left ⋙ Modules.restrictToScheme sq.left.left ⋙
          Scheme.Modules.toRingedSpace sq.left.left.left)).HasLeftDerivedFunctor (ModuleQis X)]
    [∀ sq : EtaleSquare f, DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom))] [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian Y]
    (E : ModuleDerived X)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) E)
    (hE_bounded : (t.bounded : ObjectProperty (ModuleDerived X)) E)
    (hE_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Closeds.closure
        (Modules.moduleSupport
          ((DerivedCategory.homologyFunctor (Modules X) i).obj E))))
    (a b : ℤ) (hE_tor : HasTorAmplitudeInOver f E a b) :
    IsPerfect ((Modules.pushforwardDerived f).obj E) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
