/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Normalized
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Split
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical Dold--Kan image models for cosimplicial cochains

This compatibility facade exposes the canonical degenerate cochain image, its split retract, and
the corresponding normalized quotient. Source-facing comparisons live in the separate `Compat`
facade so that canonical image clients do not inherit the degreewise span layer.

@stack 019I
-/

@[expose] public section

/- 019I: canonical Dold--Kan image API facade. -/
