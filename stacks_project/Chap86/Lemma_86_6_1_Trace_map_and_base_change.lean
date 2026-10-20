module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.BaseChange.Trace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

/- Lemma 86.6.1 (Trace map and base change): in cartesian diagram 86.4.0.1 of
algebraic spaces over a scheme S, the whiskered counits 1 ⋆ Tr_f and Tr_{f'} ⋆ 1
agree after the canonical base-change maps β = map and
α = DerivedBaseChange.map fAdj f'Adj baseChangeIso.symm. Equivalently, for every
K the composite β at a(K), then Rf'_*(α_K), then Tr_{f'} at Lg^* K, equals
Lg^*(Tr_{f,K}). -/
@[stacks 0E5L] #check
  (@AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange.map_app_comp_counit :
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
      (baseChangeIso :
        pushforwardCohomologyIn f ⋙ pullback g ≅
          pullback g' ⋙ pushforwardCohomologyIn f')
      (h_baseChange : baseChangeIso.hom =
        AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange.map g' f' f g sq.toCommSq)
      (K : DerivedQCoh Y),
      (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange.map g' f' f g sq.toCommSq).app
          (a.obj K) ≫
          (pushforwardCohomologyIn f').map
            ((CategoryTheory.DerivedBaseChange.map fAdj f'Adj baseChangeIso.symm).app K) ≫
        f'Adj.counit.app ((pullback g).obj K) =
      (pullback g).map (fAdj.counit.app K))
