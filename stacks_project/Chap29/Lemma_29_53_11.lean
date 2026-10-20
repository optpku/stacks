/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Pushforward.Integral
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.53.11: if `f : X ⟶ S` is quasi-compact, quasi-separated, and universally closed,
then `f_* 𝒪_X` is integral over `𝒪_S`. Thus the normalization of `S` in `X` is the
factorization `X ⟶ Spec_S(f_* 𝒪_X) ⟶ S`. -/
@[stacks 03GQ] #check
  (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra_isIntegral_of_universallyClosed :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
      [UniversallyClosed f],
      (Scheme.pushforwardStructureSheafQcAlgebra f).IsIntegral)
