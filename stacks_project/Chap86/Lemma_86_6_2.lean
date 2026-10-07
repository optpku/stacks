module

public import stacks_project.Chap86.Lemma_86_6_2_Unit
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

/- Lemma 86.6.2: in cartesian diagram 86.4.0.1 of algebraic spaces over a scheme S,
the whiskered units 1 ⋆ η_f : L(g')^* ⟶ L(g')^* ∘ a ∘ Rf_* and
η_{f'} ⋆ 1 : L(g')^* ⟶ a' ∘ Rf'_* ∘ L(g')^* agree after
α = DerivedBaseChange.map fAdj f'Adj baseChangeIso.symm (86.4.1.1) and
β = map (Cohomology on Sites, Remark 21.19.3). Here 1 ⋆ η_f is the left unitor
inverse followed by whiskerRight of fAdj.unit, and η_{f'} ⋆ 1 is the right unitor
inverse followed by whiskerLeft of f'Adj.unit. Equivalently the square of
natural transformations commutes. -/
@[stacks 0E5M] #check
  (@AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange.unit_baseChange :
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
      (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
      (baseChangeIso :
        pushforwardCohomologyIn f ⋙ pullback g ≅
          pullback g' ⋙ pushforwardCohomologyIn f')
      (h_baseChange : baseChangeIso.hom =
        AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange.map g' f' f g sq.toCommSq),
      (pullback g').leftUnitor.inv ≫
            Functor.whiskerRight fAdj.unit (pullback g') ≫
            (Functor.associator (pushforwardCohomologyIn f) a (pullback g')).hom ≫
            Functor.whiskerLeft (pushforwardCohomologyIn f)
              (CategoryTheory.DerivedBaseChange.map fAdj f'Adj baseChangeIso.symm) ≫
            (Functor.associator (pushforwardCohomologyIn f) (pullback g) a').inv ≫
          Functor.whiskerRight
            (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange.map g' f' f g sq.toCommSq) a' =
        (pullback g').rightUnitor.inv ≫
            Functor.whiskerLeft (pullback g') f'Adj.unit ≫
          (Functor.associator (pullback g') (pushforwardCohomologyIn f') a').inv)
