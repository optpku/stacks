/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.Restriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

/- Lemma 48.8.3 -/
@[stacks 0B6Q] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pullbackTensorDualityMapRestrictionIsIso :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
      [AlgebraicGeometry.IsNoetherian Y]
      (f : X ⟶ Y) [AlgebraicGeometry.IsProper f]
      [HomotopyTensorDescends X.toRingedSpace]
      [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      [HomotopyTensorDescends Y.toRingedSpace]
      [TensorDescends Y.toRingedSpace]
      [IsLocalization Y.toRingedSpace]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (AlgebraicGeometry.RingedSpace.opensRingedSiteHom f.toShHom)]
      [CategoryTheory.Functor.Monoidal
        (AlgebraicGeometry.RingedSpace.modulePullbackDerived f.toShHom)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (V : Y.Opens) [IsIso (f ∣_ V)]
      (K : DerivedQCoh.Plus Y),
      IsIso
        ((pullback (f ⁻¹ᵁ V).ι).map
          (pullbackTensorDualityMap f a aAdjunction
            ((DerivedCategory.Plus.CohomologyIn.toUnbounded
              Y.toRingedSpace.quasiCoherentModuleProperty).obj K))))
