/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local
public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_20_7_BaseChange

/-!
# Fpqc descent of relative Tor-amplitude on algebraic spaces

Relative Tor-amplitude in a fixed interval, and locally finite relative Tor
dimension, may be checked after derived pullback along an fpqc covering of the
base.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory
open RingedSpace.ModuleDerived (LocallyHasFiniteTorDimension relativeRestriction)

universe u v

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- A derived `𝒪_X`-module locally has finite Tor dimension as an object of
`D(f⁻¹ 𝒪_Y)` when every étale scheme square over `f` has that property after
restriction to the source chart and to the inverse-image structure sheaf of the
chart morphism. -/
def HasLocallyFiniteTorDimensionOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived
        (SmallEtaleModuleGlueing.restrictFunctor_hom sq.left ⋙ Modules.restrictToScheme sq.left.left ⋙
          Scheme.Modules.toRingedSpace sq.left.left.left)).HasLeftDerivedFunctor (ModuleQis X)]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] (E : ModuleDerived X) : Prop :=
  ∀ sq : EtaleSquare f,
    LocallyHasFiniteTorDimension
      (X := RingedSpace.Hom.inverseImageBase sq.map.left.toShHom)
      ((relativeRestriction (sq.map.left).toShHom).obj
        ((restrictToEtaleChart sq.left).obj E))

/-- Locally finite relative Tor dimension unfolds to the étale-chart ringed-space
condition along each scheme morphism of an `EtaleSquare`. -/
theorem hasLocallyFiniteTorDimensionOver_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived
        (SmallEtaleModuleGlueing.restrictFunctor_hom sq.left ⋙ Modules.restrictToScheme sq.left.left ⋙
          Scheme.Modules.toRingedSpace sq.left.left.left)).HasLeftDerivedFunctor (ModuleQis X)]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] (E : ModuleDerived X) :
    HasLocallyFiniteTorDimensionOver f E ↔
      ∀ sq : EtaleSquare f,
        LocallyHasFiniteTorDimension
          (X := RingedSpace.Hom.inverseImageBase sq.map.left.toShHom)
          ((relativeRestriction (sq.map.left).toShHom).obj
            ((restrictToEtaleChart sq.left).obj E)) :=
  sorry

/-- Lemma 76.54.2 (1): for a scheme `S`, an fpqc covering `family` of an algebraic
space `Y` over `S` with members `g_i = (family i).hom`, a morphism `f : X ⟶ Y` of
algebraic spaces, and `E` in `D_QCoh(𝒪_X)`, the following are equivalent:
`E` has tor amplitude in `[a, b]` as an object of `D(f⁻¹ 𝒪_Y)`, and each
`L(g'_i)^* E` has tor amplitude in `[a, b]` as an object of `D(f_i⁻¹ 𝒪_{Y_i})`.
Here `X_i` is the fibre product `Y_i ×_Y X` with projections
`f_i = overPullbackFst f (family i) : X_i ⟶ Y_i` and
`g'_i = overPullbackSnd f (family i) : X_i ⟶ X`, and
`L(g'_i)^*` is `modulePullbackDerived g'_i`. -/
@[stacks 0DL2]
theorem hasTorAmplitudeInOver_iff_fpqcCovering
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {ι : Type v}
    (f : X ⟶ Y) (family : ι → Over Y) (hfamily : FpqcCovering family)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived
        (SmallEtaleModuleGlueing.restrictFunctor_hom sq.left ⋙ Modules.restrictToScheme sq.left.left ⋙
          Scheme.Modules.toRingedSpace sq.left.left.left)).HasLeftDerivedFunctor (ModuleQis X)]
    [∀ sq : EtaleSquare f, DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom))]
    [∀ i : ι, ∀ sq : EtaleSquare (overPullbackFst f (family i)),
      (Functor.Homotopy.toDerived
        (SmallEtaleModuleGlueing.restrictFunctor_hom sq.left ⋙ Modules.restrictToScheme sq.left.left ⋙
          Scheme.Modules.toRingedSpace sq.left.left.left)).HasLeftDerivedFunctor
            (ModuleQis (overPullbackObj f (family i)))]
    [∀ i : ι, ∀ sq : EtaleSquare (overPullbackFst f (family i)),
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom))]
    (E : ModuleDerived X) (hE : derivedQuasiCoherentModuleProperty X E)
    (a b : ℤ) :
    HasTorAmplitudeInOver f E a b ↔
      ∀ i, HasTorAmplitudeInOver (overPullbackFst f (family i))
        ((modulePullbackDerived (overPullbackSnd f (family i))).obj E) a b :=
  sorry

/-- Lemma 76.54.2 (2): for a scheme `S`, an fpqc covering `family` of an algebraic
space `Y` over `S` with members `g_i = (family i).hom`, a morphism `f : X ⟶ Y` of
algebraic spaces, and `E` in `D_QCoh(𝒪_X)`, `E` has locally finite tor dimension
as an object of `D(f⁻¹ 𝒪_Y)` if and only if each `L(g'_i)^* E` has locally finite
tor dimension as an object of `D(f_i⁻¹ 𝒪_{Y_i})`. Here `X_i` is the fibre product
`Y_i ×_Y X` with projections `f_i = overPullbackFst f (family i) : X_i ⟶ Y_i` and
`g'_i = overPullbackSnd f (family i) : X_i ⟶ X`, and `L(g'_i)^*` is
`modulePullbackDerived g'_i`. -/
@[stacks 0DL2]
theorem locallyFiniteTorDimensionOver_iff_fpqcCovering
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {ι : Type v}
    (f : X ⟶ Y) (family : ι → Over Y) (hfamily : FpqcCovering family)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived
        (SmallEtaleModuleGlueing.restrictFunctor_hom sq.left ⋙ Modules.restrictToScheme sq.left.left ⋙
          Scheme.Modules.toRingedSpace sq.left.left.left)).HasLeftDerivedFunctor (ModuleQis X)]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))]
    [∀ i : ι, ∀ sq : EtaleSquare (overPullbackFst f (family i)),
      (Functor.Homotopy.toDerived
        (SmallEtaleModuleGlueing.restrictFunctor_hom sq.left ⋙ Modules.restrictToScheme sq.left.left ⋙
          Scheme.Modules.toRingedSpace sq.left.left.left)).HasLeftDerivedFunctor
            (ModuleQis (overPullbackObj f (family i)))]
    [∀ i : ι, ∀ sq : EtaleSquare (overPullbackFst f (family i)),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))]
    (E : ModuleDerived X) (hE : derivedQuasiCoherentModuleProperty X E) :
    HasLocallyFiniteTorDimensionOver f E ↔
      ∀ i, HasLocallyFiniteTorDimensionOver (overPullbackFst f (family i))
        ((modulePullbackDerived (overPullbackSnd f (family i))).obj E) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
