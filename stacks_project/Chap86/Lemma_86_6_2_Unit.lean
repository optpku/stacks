module

public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import stacks_project.Chap86.Lemma_86_4_1_BaseChange

/-!
# Units and derived base change on algebraic spaces

For a Tor-independent cartesian square of algebraic spaces, the adjunction units
commute with the inverse mate of an explicitly chosen base-change isomorphism and
the corresponding canonical derived base-change map on `DerivedQCoh`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange

/-- For a Tor-independent cartesian square of algebraic spaces, the adjunction units
commute with the inverse mate of an explicitly chosen base-change isomorphism and
the corresponding canonical base-change map.

Here `η_f` is the unit of `fAdj`, `β` is `map`, and `α` is
`CategoryTheory.DerivedBaseChange.map fAdj f'Adj baseChangeIso.symm`, equivalently
the `mapOfRight` construction of 86.4.1.1 from the inverse of `rightMate`. The
whiskered unit `1 ⋆ η_f` is the left unitor inverse followed by `whiskerRight` of
`fAdj.unit`, and `η_{f'} ⋆ 1` is the right unitor inverse followed by `whiskerLeft`
of `f'Adj.unit`. -/
theorem unit_baseChange
    {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (baseChangeIso :
      pushforwardCohomologyIn f ⋙ pullback g ≅
        pullback g' ⋙ pushforwardCohomologyIn f')
    (h_baseChange : baseChangeIso.hom = map g' f' f g sq.toCommSq) :
    (pullback g').leftUnitor.inv ≫
          Functor.whiskerRight fAdj.unit (pullback g') ≫
          (Functor.associator (pushforwardCohomologyIn f) a (pullback g')).hom ≫
          Functor.whiskerLeft (pushforwardCohomologyIn f)
            (CategoryTheory.DerivedBaseChange.map fAdj f'Adj baseChangeIso.symm) ≫
          (Functor.associator (pushforwardCohomologyIn f) (pullback g) a').inv ≫
        Functor.whiskerRight (map g' f' f g sq.toCommSq) a' =
      (pullback g').rightUnitor.inv ≫
          Functor.whiskerLeft (pullback g') f'Adj.unit ≫
        (Functor.associator (pullback g') (pushforwardCohomologyIn f') a').inv :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange
