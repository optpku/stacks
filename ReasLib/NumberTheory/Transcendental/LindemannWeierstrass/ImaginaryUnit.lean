/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.IsIntegral
public import Mathlib.RingTheory.Algebraic.Integral

@[expose] public section

namespace LindemannWeierstrass

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for PI-15:
- primary domain: algebraicity of distinguished complex numbers over `ℚ`;
- sampled owner declarations:
  `Complex.isIntegral_rat_I`,
  `IsIntegral.isAlgebraic`,
  `Algebra.IsIntegral.isAlgebraic`;
- best owner abstraction: the owner predicate `IsIntegral ℚ Complex.I`, with `IsAlgebraic` as the
  canonical derived view used by the source statement;
- primitive data: the standard integrality theorem `Complex.isIntegral_rat_I`;
- derived API: algebraicity of `Complex.I` over `ℚ` via `IsIntegral.isAlgebraic`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that `Complex.I` is algebraic over `ℚ`;
- `core/canonical`: `Complex.isIntegral_rat_I`;
- `bridge/view`: `IsIntegral.isAlgebraic`;
- `layer`: `source-facing` for the theorem below.
-/

/-- Lemma PI-15: the complex number `Complex.I` is algebraic over `ℚ`. -/
theorem complex_I_isAlgebraic_over_rat : IsAlgebraic ℚ Complex.I :=
  Complex.isIntegral_rat_I.isAlgebraic

end LindemannWeierstrass
