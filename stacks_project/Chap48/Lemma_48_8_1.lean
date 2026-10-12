/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 48.8.1 (1): the comparison `Lf^*K ⊗ᴸ a(L) ⟶ a(K ⊗ᴸ L)` is an isomorphism when `K` is perfect. -/
@[stacks 0A9T] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pullbackTensorRightAdjointMap_isIso_of_isPerfect :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
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
      (K L : DerivedQCoh Y) (hK : RingedSpace.ModuleDerived.IsPerfect K.obj),
      IsIso (pullbackTensorRightAdjointMap f a aAdjunction K L))

/- Lemma 48.8.1 (2): the structure-sheaf specialization `Lf^*K ⊗ᴸ a(𝒪_Y) ⟶ a(K)` is an isomorphism when `K` is perfect. -/
@[stacks 0A9T] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pullbackTensorDualityMap_isIso_of_isPerfect :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
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
      (K : DerivedQCoh Y) (hK : RingedSpace.ModuleDerived.IsPerfect K.obj),
      IsIso (pullbackTensorDualityMap f a aAdjunction K))

end AlgebraicGeometry.Scheme.DerivedQCoh
