module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.BaseChange
public import ReasLib.CategoryTheory.Adjunction.BaseChange

/-!
# Trace maps and derived base change on algebraic spaces

For a Tor-independent cartesian square of algebraic spaces, the canonical
derived base-change map, the inverse mate, and the target counit recover the
pullback of the source counit on `DerivedQCoh`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange

/-- For a Tor-independent cartesian square of algebraic spaces, the canonical
derived base-change map followed by the inverse mate and the target counit
equals the pullback of the source counit.

Here `Tr_f` is the counit of `fAdj`, `β` is `map`, and `α` is
`CategoryTheory.DerivedBaseChange.map fAdj f'Adj baseChangeIso.symm`. -/
theorem map_app_comp_counit
    {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (baseChangeIso :
      pushforwardCohomologyIn f ⋙ pullback g ≅
        pullback g' ⋙ pushforwardCohomologyIn f')
    (h_baseChange : baseChangeIso.hom = map g' f' f g sq.toCommSq)
    (K : DerivedQCoh Y) :
    (map g' f' f g sq.toCommSq).app (a.obj K) ≫
        (pushforwardCohomologyIn f').map
          ((CategoryTheory.DerivedBaseChange.map fAdj f'Adj baseChangeIso.symm).app K) ≫
      f'Adj.counit.app ((pullback g).obj K) =
    (pullback g).map (fAdj.counit.app K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange
