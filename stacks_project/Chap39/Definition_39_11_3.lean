/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Torsor

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 39.11.3 (1): A pseudo `G`-torsor is a principal homogeneous space,
or `G`-torsor, when it acquires sections on an fpqc cover. -/
@[stacks 049A] #check
  (AlgebraicGeometry.GroupScheme.isTorsor_iff :
    ∀ {S : Scheme.{u}} (G : Grp (Over S)) (X : Mod (Over S) G.X),
      AlgebraicGeometry.GroupScheme.IsTorsor G X ↔
        Mod.IsPseudoTorsor X ∧
          ∃ U : S.Cover.{u} Scheme.fpqcPrecoverage,
            ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X))

/- Definition 39.11.3 (2): For one of the five standard topologies `τ`, a pseudo
`G`-torsor is a `τ`-torsor when it acquires sections on a `τ`-cover. -/
@[stacks 049A] #check
  (AlgebraicGeometry.GroupScheme.isStandardTorsor_iff :
    ∀ {S : Scheme.{u}} (G : Grp (Over S)) (X : Mod (Over S) G.X)
        (τ : AlgebraicGeometry.StandardTopology),
      AlgebraicGeometry.GroupScheme.IsStandardTorsor G X τ ↔
        Mod.IsPseudoTorsor X ∧
          ∃ U : S.Cover.{u} τ.precoverage,
            ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X))

/- Definition 39.11.3 (3): An fpqc `G`-torsor is quasi-isotrivial when it is an
étale torsor. -/
@[stacks 049A] #check
  (AlgebraicGeometry.GroupScheme.isQuasiIsotrivial_iff :
    ∀ {S : Scheme.{u}} (G : Grp (Over S)) (X : Mod (Over S) G.X),
      AlgebraicGeometry.GroupScheme.IsQuasiIsotrivial G X ↔
        Mod.IsPseudoTorsor X ∧
          ∃ U : S.Cover.{u} AlgebraicGeometry.StandardTopology.etale.precoverage,
            ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X))

/- Definition 39.11.3 (4): An fpqc `G`-torsor is locally trivial when it is a
Zariski torsor. -/
@[stacks 049A] #check
  (AlgebraicGeometry.GroupScheme.isLocallyTrivial_iff :
    ∀ {S : Scheme.{u}} (G : Grp (Over S)) (X : Mod (Over S) G.X),
      AlgebraicGeometry.GroupScheme.IsLocallyTrivial G X ↔
        Mod.IsPseudoTorsor X ∧
          ∃ U : S.Cover.{u} AlgebraicGeometry.StandardTopology.zariski.precoverage,
            ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X))
