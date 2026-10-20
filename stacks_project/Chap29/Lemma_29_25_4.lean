/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Pushforward
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.25.4: Let `f : X ⟶ Y` be an affine morphism over `S`, and let `ℱ` be a
quasi-coherent `𝒪_X`-module. Then `ℱ` is flat over `S` if and only if `f_*ℱ` is flat over `S`. -/
@[stacks 0FLM] #check
  (AlgebraicGeometry.Scheme.Modules.flatOver_iff_pushforward_flatOver_of_isAffineHom :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsAffineHom f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      Scheme.Modules.flatOver ℱ (f ≫ g) ↔
        Scheme.Modules.flatOver ((Scheme.Modules.pushforward f).obj ℱ) g)
