/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Scheme gluing support

Import facade for Mathlib scheme gluing. Basis-indexed gluing and relative-module
comparisons remain separate leaves, so importing this facade does not pull in that
infrastructure.
-/

@[expose] public section
