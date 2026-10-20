/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Faithful
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.OverBase

/-!
# Relatively representable morphisms of categories fibred in groupoids

Compatibility aggregate for the ordinary fixed-universe, faithfulness, and
heterogeneous-boundary APIs. Import `RelativelyRepresentable.BaseChange` for ordinary base-change
and closure statements, `RelativelyRepresentable.Faithful` for the narrow 02Y8 consequence, or
`RelativelyRepresentable.OverBase` when a universe-saturated boundary is required.
-/
