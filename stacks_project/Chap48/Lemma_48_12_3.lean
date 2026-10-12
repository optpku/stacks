/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.ProperFlat
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

universe u

/- Lemma 48.12.3: if `f : X ⟶ Y` is proper, flat, and of finite presentation over
a quasi-compact and quasi-separated scheme, then the comparison
`Lf^* K ⊗ᴸ a(𝒪_Y) ⟶ a(K)` is an isomorphism for every `K : DerivedQCoh Y`. -/
@[stacks 0E4K] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pullbackTensorDualityMapIsIsoOfProperFlat :
    ∀ {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
      (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
      [HomotopyTensorDescends X.toRingedSpace]
      [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      [HomotopyTensorDescends Y.toRingedSpace]
      [TensorDescends Y.toRingedSpace]
      [IsLocalization Y.toRingedSpace]
      [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      (a : AlgebraicGeometry.Scheme.DerivedQCoh Y ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh X)
      (aAdjunction : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (K : AlgebraicGeometry.Scheme.DerivedQCoh Y),
      IsIso (AlgebraicGeometry.Scheme.DerivedQCoh.pullbackTensorDualityMap
        f a aAdjunction K))
