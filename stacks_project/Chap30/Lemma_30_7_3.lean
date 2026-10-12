/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.UniversalBaseChange
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.7.3: if `f : X ⟶ S` is quasi-compact and quasi-separated and `S` is
quasi-compact and separated, then every quasicoherent `𝒪_X`-module admits a
bounded-below complex of quasicoherent `𝒪_S`-modules whose pullback along every
`g : S' ⟶ S` represents the derived pushforward of the base-changed module. -/
@[stacks 01XN] #check
  (AlgebraicGeometry.Scheme.exists_universalDerivedPushforwardComplex :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
      [CompactSpace S.carrier] [S.IsSeparated]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      ∃ K : CochainComplex.Plus S.Modules,
        AlgebraicGeometry.Scheme.IsUniversalDerivedPushforwardComplex f ℱ K)
