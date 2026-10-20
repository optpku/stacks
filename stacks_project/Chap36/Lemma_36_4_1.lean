/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.CohomologicalDimension
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Derived pushforward along a qcqs morphism, restricted to derived modules with
quasi-coherent cohomology. -/
noncomputable abbrev pushforward {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f] :
    DerivedQCoh X ⥤ DerivedQCoh S :=
  pushforwardCohomologyIn f

/- Lemma 36.4.1 (1): derived pushforward along a quasi-compact and quasi-separated
morphism of schemes preserves quasi-coherent cohomology. -/
@[stacks 08D5] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn.mapsTo :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f],
      derivedQuasiCoherentModuleProperty X ≤
        (derivedQuasiCoherentModuleProperty S).inverseImage
          (RingedSpace.moduleDerivedPushforward f.toShHom))

/- Lemma 36.4.1 (2): over a quasi-compact base, derived pushforward along a
quasi-compact and quasi-separated morphism has a uniform upper cohomological bound on
objects whose positive cohomology vanishes. -/
@[stacks 08D5] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn.uniformUpperBound :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      [CompactSpace S],
      ∃ N : ℤ, ∀ E : DerivedQCoh X,
        E.obj.IsLE 0 → ((pushforward f).obj E).obj.IsLE (N - 1))

/- Lemma 36.4.1 (3): the upper cohomological bound for derived pushforward can be
chosen uniformly after every base change. -/
@[stacks 08D5] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn.baseChangeUpperBound :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      [CompactSpace S],
      ∃ N : ℤ, ∀ ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S)
        (E : DerivedQCoh (pullback f g)),
        E.obj.IsLE 0 →
          ((pushforward (pullback.snd f g)).obj E).obj.IsLE (N - 1))

end AlgebraicGeometry.Scheme.DerivedQCoh
