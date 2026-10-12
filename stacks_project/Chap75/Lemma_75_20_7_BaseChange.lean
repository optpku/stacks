/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap75.Definition_75_20_2_TorIndependence
public import stacks_project.Chap75.Lemma_75_26_4_Pullback

/-!
# Tor-independent base change of relative Tor-amplitude on algebraic spaces

Derived pullback along a Tor-independent cartesian square of algebraic spaces
preserves relative Tor-amplitude in a fixed interval `[a, b]`. A module flat over
the base computes that derived pullback already at its degree-zero complex.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Restriction of `𝒪_X`-modules along an étale scheme chart, viewed on the
underlying ringed space, is additive. -/
instance instAdditive_restrictToEtaleChart {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    (Modules.restrictToScheme U ⋙ Scheme.Modules.toRingedSpace U.left.left).Additive :=
  sorry

/-- Homotopy-to-derived restriction along an étale scheme chart has a total left
derived functor. -/
instance instHasLeftDerivedFunctor_restrictToEtaleChart
    {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    (Functor.Homotopy.toDerived
      (Modules.restrictToScheme U ⋙
        Scheme.Modules.toRingedSpace U.left.left)).HasLeftDerivedFunctor
      (ModuleQis X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Derived restriction of an `𝒪_X`-module along an étale scheme chart, as a
complex of modules on the underlying ringed space of the chart. -/
def restrictToEtaleChart {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    ModuleDerived X ⥤ RingedSpace.ModuleDerived U.left.left.toRingedSpace :=
  (Functor.Homotopy.toDerived
      (Modules.restrictToScheme U ⋙
        Scheme.Modules.toRingedSpace U.left.left)).totalLeftDerived
    DerivedCategory.Qh (ModuleQis X)

/-- Derived restriction along an étale scheme chart is the total left derived
functor of underived chart restriction to the underlying ringed space. -/
theorem restrictToEtaleChart_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    restrictToEtaleChart U =
      (Functor.Homotopy.toDerived
          (Modules.restrictToScheme U ⋙
            Scheme.Modules.toRingedSpace U.left.left)).totalLeftDerived
        DerivedCategory.Qh (ModuleQis X) :=
  sorry

/-- A derived `𝒪_X`-module has Tor-amplitude in `[a, b]` as a complex of
`f⁻¹ 𝒪_Y`-modules when every étale scheme square over `f` has that relative
Tor-amplitude after restriction to the source chart. -/
def HasTorAmplitudeInOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (E : ModuleDerived X) (a b : ℤ) : Prop :=
  ∀ sq : EtaleSquare f,
    RingedSpace.ModuleDerived.HasTorAmplitudeInOver sq.map.left.toShHom
      ((restrictToEtaleChart sq.left).obj E) a b

/-- Relative Tor-amplitude in `[a, b]` unfolds to the étale-chart ringed-space
condition along each scheme morphism of an `EtaleSquare`. -/
theorem hasTorAmplitudeInOver_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (E : ModuleDerived X) (a b : ℤ) :
    HasTorAmplitudeInOver f E a b ↔
      ∀ sq : EtaleSquare f,
        RingedSpace.ModuleDerived.HasTorAmplitudeInOver sq.map.left.toShHom
          ((restrictToEtaleChart sq.left).obj E) a b :=
  sorry

/-- Flatness of an `𝒪_X`-module over `Y` is Tor-amplitude in `[0, 0]` as a
complex of `f⁻¹ 𝒪_Y`-modules. -/
theorem hasTorAmplitudeInOver_single_iff_flatOver {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (𝒢 : X.Modules) :
    Modules.flatOver 𝒢 f ↔
      HasTorAmplitudeInOver f ((DerivedCategory.singleFunctor (Modules X) 0).obj 𝒢)
        0 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- In a Tor-independent cartesian square of algebraic spaces, derived pullback
preserves a fixed Tor-amplitude interval relative to the base. -/
theorem hasTorAmplitudeInOver
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (E : ModuleDerived X) (a b : ℤ)
    (hE : ModuleDerived.HasTorAmplitudeInOver f E a b) :
    ModuleDerived.HasTorAmplitudeInOver f' ((modulePullbackDerived g').obj E) a b :=
  sorry

/-- In a Tor-independent cartesian square of algebraic spaces, a module flat over
the base computes derived pullback at its degree-zero complex. -/
theorem computesAtSingle
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (𝒢 : X.Modules) (h𝒢 : Modules.flatOver 𝒢 f) :
    Functor.LeftDerived.ComputesAt (modulePullbackToDerived g') (ModuleQis X)
      ((HomotopyCategory.singleFunctor (Modules X) 0).obj 𝒢) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange
