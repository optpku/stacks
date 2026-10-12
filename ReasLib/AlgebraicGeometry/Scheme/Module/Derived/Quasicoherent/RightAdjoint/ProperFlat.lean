/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.Coproduct

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a proper, flat, finitely presented morphism with quasi-compact and quasi-separated
target, the tensor-duality comparison is invertible for every derived quasicoherent object. -/
theorem pullbackTensorDualityMapIsIsoOfProperFlat
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace]
    [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    IsIso (pullbackTensorDualityMap f a aAdjunction K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
