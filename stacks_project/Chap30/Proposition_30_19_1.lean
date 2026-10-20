/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Coherent
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Proposition 30.19.1: let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be a proper
morphism, and let `ℱ` be a coherent `𝒪_X`-module. Then every higher direct image
`R^i f_* ℱ` is a coherent `𝒪_S`-module. -/
@[stacks 02O5] #check
  (AlgebraicGeometry.Scheme.higherDirectImageModule_isCoherent_of_proper :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [IsLocallyNoetherian S] [IsProper f]
      (ℱ : X.Modules) [ℱ.IsCoherent] (i : ℕ),
      (RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ i).IsCoherent)
