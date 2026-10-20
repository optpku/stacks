/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints.Finiteness

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules TopologicalSpace
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.2.8: let `S` be a scheme, let `X` be a locally Noetherian algebraic space
over `S`, and let `F` be a coherent `𝒪_X`-module. Then `Ass(F) ∩ W` is finite for every
quasi-compact open `W ⊆ |X|`. On a locally Noetherian algebraic space, `Ass(F)` is
`F.weakAss`. -/
@[stacks 0CUN] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.associatedPoints_inter_quasiCompactOpen_finite :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
      (F : X.Modules) [F.IsCoherent] (W : Opens |X|),
      IsCompact (W : Set |X|) → (F.weakAss ∩ (W : Set |X|)).Finite)
