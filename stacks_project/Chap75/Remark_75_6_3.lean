/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.SchemePushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme.Pullback

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import stacks_project.Chap36.Lemma_36_4_1
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap75.Lemma_75_4_2_Pullback
public import stacks_project.Chap75.Lemma_75_5_5
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward

/-!
# Matching derived pullback and pushforward for representable algebraic spaces

A morphism of representable algebraic spaces over `S` is represented by a morphism
of schemes `f0 : X0 ⟶ Y0`. Lemma 75.4.2 identifies `D_QCoh(𝒪_{X0})` with
`D_QCoh(𝒪_X)` via `ε*` along the flat morphism of ringed sites from the small
étale site of `ofOver X0` to the Zariski site of `X0.left`, and likewise for `Y`.
Derived pullback always commutes with these identifications; if `f0` is
quasi-compact and quasi-separated, equivalently if `ofOverMap f0` is, derived
pushforward commutes as well.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The canonical exact inverse-image comparison for a represented algebraic space. -/
noncomputable abbrev ofOverEpsilonStar {S : Scheme.{u}} (U : Over S) :
    Scheme.DerivedQCoh U.left ⥤ DerivedQCoh (ofOver U) :=
  schemeToSpaceDerived U

/- Remark 75.6.3 (1): the canonical étale-to-Zariski equivalences commute naturally
with derived pullback along every morphism represented by schemes. -/
@[stacks 08GH] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SchemeRestriction.epsilonPullbackQCohIso :
    ∀ {S : Scheme.{u}} {Y0 X0 : Over S} (f0 : X0 ⟶ Y0),
      (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.schemeToSpaceDerived Y0 ⋙
        AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pullback (ofOverMap f0)) ≅
      (AlgebraicGeometry.Scheme.DerivedQCoh.pullback f0.left ⋙
        AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.schemeToSpaceDerived X0))

/- Remark 75.6.3 (2): the canonical étale-to-Zariski equivalences commute naturally
with derived pushforward for quasi-compact, quasi-separated morphisms. -/
@[stacks 08GH] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.ofOver_pushforward_comm :
    ∀ {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
      [QuasiCompact (ofOverMap f0)] [QuasiSeparated (ofOverMap f0)],
      IsIsomorphic
        (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f0.left ⋙
          AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.schemeToSpaceDerived Y0)
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.schemeToSpaceDerived X0 ⋙
          AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardCohomologyIn (ofOverMap f0)))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
