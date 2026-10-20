module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

/- Lemma 86.7.2: for a Tor-independent cartesian square of algebraic spaces, the canonical
tensor-duality comparisons commute with derived base change. -/
@[stacks 0E5R] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pullbackTensorDualityMap_baseChange :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (K : DerivedQCoh Y),
    CommSq
      ((pullback g').map (pullbackTensorDualityMap f a fAdj K))
      (pullbackTensorDualityBaseChangeMap g' f' f g sq a a' fAdj f'Adj hTor K)
      ((BaseChange.twistedMap g' f' f g sq a a' fAdj f'Adj hTor).app K)
      (pullbackTensorDualityMap f' a' f'Adj ((pullback g).obj K)))
