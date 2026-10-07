module

public import stacks_project.Chap86.Lemma_86_4_1_BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

/- Lemma 86.4.1: in cartesian diagram 86.4.0.1 of algebraic spaces over a scheme S,
with Y' and X Tor independent over Y, the right-adjoint mate
a' ⋙ pushforwardCohomologyIn g' ⟶ pushforwardCohomologyIn g ⋙ a of ordinary
derived base change is an isomorphism on DerivedQCoh. -/
@[stacks 0E5C] #check
  (@AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange.rightMate_isIso_of_torIndependent :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
      [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
      [IsIso (modulePullbackDerived.compComparison f' g)]
      [IsIso (modulePullbackDerived.compComparison g' f)]
      (sq : IsPullback g' f' f g)
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
      (fAdj : pushforwardCohomologyIn f ⊣ a)
      (f'Adj : pushforwardCohomologyIn f' ⊣ a')
      (hTor : TorIndependentOver (Over.mk f) (Over.mk g)),
      IsIso
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange.rightMate
          g' f' f g sq.toCommSq a a' fAdj f'Adj))
