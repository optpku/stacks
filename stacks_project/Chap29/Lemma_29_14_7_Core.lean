/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.Local
import Mathlib.Tactic.Recall

/-
Lemma 29.14.7 (1), (2), and (5) are now owned by the general ring-homomorphism
API. The source-facing conditions become `RingHom.IsIsoOnLocalRings`,
`RingHom.Locally RingHom.IsStandardOpenImmersion`, and
`RingHom.TargetIsNoetherian`, respectively.
-/
recall RingHom.IsIsoOnLocalRings
recall RingHom.IsIsoOnLocalRings.propertyIsLocal
recall RingHom.locallyStandardOpenImmersion_propertyIsLocal
recall RingHom.TargetIsNoetherian
recall RingHom.TargetIsNoetherian.propertyIsLocal
