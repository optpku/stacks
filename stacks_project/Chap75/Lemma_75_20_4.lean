module

public import stacks_project.Chap75.Lemma_75_20_4_BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 75.20.4: for a cartesian square of algebraic spaces over a scheme `S`
whose vertical map `f : X ⟶ Y` is quasi-compact and quasi-separated, Tor
independence of `X` and `Y'` over `Y` implies that the canonical derived
base-change map `Lg^* Rf_* E ⟶ Rf'_* L(g')^* E` is an isomorphism for every
`E` in `D_QCoh(𝒪_X)`. -/
@[stacks 08IR] #check
  (AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.map_app_isIso :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      [IsIso (modulePullbackDerived.compComparison f' g)]
      [IsIso (modulePullbackDerived.compComparison g' f)]
      (sq : IsPullback g' f' f g),
      TorIndependentOver (Over.mk f) (Over.mk g) →
        ∀ (E : DerivedQCoh X),
          IsIso ((DerivedBaseChange.map sq.toCommSq).app E.obj))
