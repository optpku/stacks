module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.PerfectProper
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 48.13.3: if `f : X ⟶ Y` is a perfect proper morphism of Noetherian schemes,
then the comparison `Lf^* K ⊗ᴸ a(𝒪_Y) ⟶ a(K)` is an isomorphism for every
`K : DerivedQCoh Y`. -/
@[stacks 0A9U] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pullbackTensorDualityMapIsIsoOfPerfectProper :
    ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [IsProper f] [LocallyOfType RingHom.IsPerfectRingMap f]
      [HomotopyTensorDescends X.toRingedSpace]
      [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      [HomotopyTensorDescends Y.toRingedSpace]
      [TensorDescends Y.toRingedSpace]
      [IsLocalization Y.toRingedSpace]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom f.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (K : DerivedQCoh Y),
      IsIso (pullbackTensorDualityMap f a aAdjunction K))

end AlgebraicGeometry.Scheme.DerivedQCoh
