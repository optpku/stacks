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

/-- For a perfect proper morphism of Noetherian schemes, the tensor-duality
comparison for a right adjoint to derived quasicoherent pushforward is an
isomorphism for every object of the target category. -/
noncomputable instance pullbackTensorDualityMapIsIsoOfPerfectProper
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [LocallyOfType RingHom.IsPerfectRingMap f]
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
