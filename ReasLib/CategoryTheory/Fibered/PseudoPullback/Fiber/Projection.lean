/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Projection.Forward
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Projection.Inverse

/-!
# Projection comparisons for fibres of based pseudo-pullbacks

This stable aggregate exposes both directions of the projection comparison. Consumers needing
only the concrete actual-to-modelled comparison should import `Fiber.Projection.Forward`; the
inverse direction is isolated in `Fiber.Projection.Inverse` because it depends on the packaged
fibre equivalence.
-/
