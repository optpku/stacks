/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange.TorIndependence
public import stacks_project.Chap36.Lemma_36_4_1
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TorIndependentBaseChange

/- Lemma 36.22.5: for a Tor-independent cartesian base-change square whose vertical
map is quasi-compact and quasi-separated, every quasi-coherent component of the canonical
unbounded derived base-change transformation is invertible. -/
@[stacks 08IB] #check
  (AlgebraicGeometry.Scheme.TorIndependentBaseChange.map_app_isIso :
    ∀ {X' X S' S : Scheme.{u}}
      (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
      [QuasiCompact f] [QuasiSeparated f]
      [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
      [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
      (sq : IsPullback g' f' f g)
      (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
      (E : Scheme.DerivedQCoh X),
      IsIso ((DerivedBaseChange.map sq.toCommSq).app E.obj))

end AlgebraicGeometry.Scheme.TorIndependentBaseChange
