/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normalization

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.53.7: Let `f : Y ⟶ X` be a quasi-compact and quasi-separated morphism of schemes.
Let `X'` be the normalization of `X` in `Y`. Then the normalization of `X'` in `Y` is `X'`. -/
@[stacks 0BXA] #check
  (AlgebraicGeometry.Scheme.Hom.isIso_fromNormalization_toNormalization :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f],
      IsIso ((f.toNormalization).fromNormalization))
