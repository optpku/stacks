/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open RingedSite.Hom.DerivedAdjunction

universe u

/- Lemma 36.22.9: for a Tor-independent cartesian square whose map `i : Z ⟶ X` is a
closed immersion, the canonical unbounded derived base-change transformation is invertible. -/
@[stacks 0E23] #check
  (AlgebraicGeometry.Scheme.TorIndependentBaseChange.map_isIso_of_isClosedImmersion :
    ∀ {Z' Z X' X : Scheme.{u}}
      (g : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (f : X' ⟶ X)
    [HasPair (RingedSpace.opensRingedSiteHom i.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom i'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison i'.toShHom f.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g.toShHom i.toShHom)]
    (sq : IsPullback g i' i f) [IsClosedImmersion i]
    (hTor : Scheme.TorIndependentOver (Over.mk i) (Over.mk f)),
    IsIso (Scheme.Hom.DerivedBaseChange.map sq.toCommSq))
