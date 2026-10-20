/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.NeronBlowup.Core
public import ReasLib.RingTheory.Smooth.NeronBlowup.Iterate
public import ReasLib.RingTheory.Smooth.NeronBlowup.Localization
public import ReasLib.RingTheory.Smooth.NeronBlowup.Source

@[expose] public section

/-!
# Affine Neron blowups of DVR factorizations

Stable aggregate for one-step blowups, iteration, localization, and source
base change. Clients should prefer the narrow leaf matching their use.
-/
