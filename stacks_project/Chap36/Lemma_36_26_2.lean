/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.Pushforward

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

/- Lemma 36.26.2: for a cartesian square of schemes with `f` quasi-compact and
quasi-separated, if the pointwise cohomology base-change maps for `α` are
isomorphisms, then canonical derived base change followed by `Rf'_* α` is an
isomorphism. -/
@[stacks 0DJ9] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.cohomologyBaseChange_comp_isIso :
    ∀ {X' X S' S : Scheme.{u}}
      (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
      [QuasiCompact f] [QuasiSeparated f]
      [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
      [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
      (sq : IsPullback g' f' f g) (K : Scheme.ModuleDerived.Quasicoherent X)
      (K' : Scheme.ModuleDerived.Quasicoherent X')
      (α : (Scheme.DerivedQCoh.pullback g').obj K ⟶ K')
      [∀ (x' : X') (i : ℤ),
        IsIso ((Scheme.DerivedQCoh.CohomologyBaseChangeModel.canonical
          g' f' f g sq).pointMap K K' α x' i)],
      IsIso
        ((Scheme.Hom.DerivedBaseChange.map sq.toCommSq).app K.obj ≫
          (RingedSpace.moduleDerivedPushforward f'.toShHom).map
            ((Scheme.DerivedQCoh.pullback.inclusionIso g').inv.app K ≫
              (Scheme.ModuleDerived.Quasicoherent.inclusion X').map α)))

end
