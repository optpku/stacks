/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Injective
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 110.47.2: there exists an affine scheme `X = Spec A` whose underlying
topological space is Noetherian and an injective `A`-module `I` such that
`tilde I` has nonvanishing `H^1` on some quasi-compact open `U` of `X`. -/
@[stacks 0CRZ] #check
  (AlgebraicGeometry.tilde.exists_injective_qcOpen_h1_ne_zero :
    ∃ (A : CommRingCat.{u}) (I : ModuleCat.{u} A) (U : Opens (Spec A)),
      Module.Injective A I ∧
        NoetherianSpace (Spec A) ∧
        IsCompact (U : Set (Spec A)) ∧
          ¬ IsZero (RingedSpace.moduleCohomologyOnOpen (AlgebraicGeometry.tilde I) 1 U))
