/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.FullSubbicategory.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LocallyInduced.Lift

/-!
# Induced pseudopullback-cone compatibility aggregate

This historical import path exports the focused full-subbicategory and locally induced lifts.
Concrete data and field readouts live in `FullSubbicategory.Basic` and `LocallyInduced.Lift`;
the full-subbicategory bilimit transfer instance lives in `FullSubbicategory.Bilimit`.
The locally induced universal-property criterion is intentionally owned by
`LocallyInduced.Bilimit`.

Focused consumers should import the smallest leaf matching the required interface.
-/
