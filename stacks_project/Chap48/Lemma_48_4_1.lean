/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BaseChange.RightAdjoint
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.4.1: for a cartesian square of quasi-compact quasi-separated schemes,
Tor independence of `f` and `g` makes the canonical right-adjoint base-change mate
`a' ⋙ Rg'_* ⟶ Rg_* ⋙ a` an isomorphism. -/
@[stacks 0A9K] #check
  (@AlgebraicGeometry.Scheme.DerivedQCoh.BaseChange.rightMate_isIso_of_torIndependent :
    ∀ {X' X Y' Y : Scheme.{u}}
      [CompactSpace X'] [QuasiSeparatedSpace X']
      [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y'] [QuasiSeparatedSpace Y']
      [CompactSpace Y] [QuasiSeparatedSpace Y]
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      (sq : IsPullback g' f' f g)
      (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh X)
      (a' : Scheme.DerivedQCoh Y' ⥤ Scheme.DerivedQCoh X')
      (fAdj : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (f'Adj : Scheme.DerivedQCoh.pushforwardCohomologyIn f' ⊣ a')
      (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g)),
      IsIso
        (Scheme.DerivedQCoh.BaseChange.rightMate
          g' f' f g sq.toCommSq a a' fAdj f'Adj))

/- Flatness of `g` is the source's stated sufficient condition for Tor independence. -/
#check
  (@AlgebraicGeometry.Scheme.DerivedQCoh.BaseChange.rightMate_isIso_of_flat :
    ∀ {X' X Y' Y : Scheme.{u}}
      [CompactSpace X'] [QuasiSeparatedSpace X']
      [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y'] [QuasiSeparatedSpace Y']
      [CompactSpace Y] [QuasiSeparatedSpace Y]
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) [Flat g]
      (sq : IsPullback g' f' f g)
      (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh X)
      (a' : Scheme.DerivedQCoh Y' ⥤ Scheme.DerivedQCoh X')
      (fAdj : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (f'Adj : Scheme.DerivedQCoh.pushforwardCohomologyIn f' ⊣ a'),
      IsIso
        (Scheme.DerivedQCoh.BaseChange.rightMate
          g' f' f g sq.toCommSq a a' fAdj f'Adj))
