/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatibility path for the degenerate comparison

The source-facing/canonical comparison is owned by `QImage.Comparison`, where it can be imported
without the decomposition or normalized layers.  This facade preserves the historical import path
for existing chapter files and exposes the same canonical declarations without redeclaring them.
-/

@[expose] public section

/- The historical import path re-exports the canonical comparison API. -/
