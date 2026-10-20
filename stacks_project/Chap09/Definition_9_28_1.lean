/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Galois.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 9.28.1:
- primary domain: field-extension properties in commutative algebra / field theory;
- sampled representative owner declarations:
  `Algebra.IsAlgebraic`,
  `Algebra.IsSeparable`,
  `Normal`,
  `IsGalois`;
- sampled derived/specification API:
  `Algebra.isAlgebraic_def`,
  `Algebra.isSeparable_iff`,
  `isPurelyInseparable_iff_pow_mem`,
  `normal_iff`,
  `isGalois_iff`;
- best owner abstraction: no new owner lives in this review file; it directly reuses the canonical
  extension-level owners without rebuilding their specification surface in this aggregate item;
- primitive data: none locally, since every notion named in the source is already owned upstream;
- derived API: the earlier owner files already expose the companion textbook characterizations, so
  this file should aggregate the owner layer only.

Source/core/bridge triage:
- `source-facing`: the review list of textbook notions "algebraic / separable / purely
  inseparable / normal / Galois";
- `core/canonical`: the mathlib owners named above;
- `bridge/view`: their existing specification theorems.

This item should therefore remain a pure review-check file rather than repeat companion
characterizations or introduce any parallel wrapper. -/

/- Definition 9.28.1: this review item simply recollects the earlier Chapter 9 canonical owner
notions for algebraic, separable, purely inseparable, normal, and Galois field extensions:
`Algebra.IsAlgebraic`, `Algebra.IsSeparable`, `IsPurelyInseparable`, `Normal`, and `IsGalois`. -/
@[stacks 030J]
#check Algebra.IsAlgebraic

/- Definition 9.28.1: the textbook notion that an algebraic field extension is separable is the
canonical mathlib typeclass `Algebra.IsSeparable`; algebraicity is absorbed canonically by the
pointwise separability condition. -/
#check Algebra.IsSeparable

/- Definition 9.28.1: in positive characteristic, the textbook notion that an algebraic field
extension is purely inseparable is the canonical mathlib typeclass `IsPurelyInseparable`, which
again packages algebraicity canonically. -/
#check IsPurelyInseparable

/- Definition 9.28.1: the textbook notion that an algebraic field extension is normal is the
canonical field-extension class `Normal`, which already packages algebraicity. -/
#check Normal

/- Definition 9.28.1: a Galois extension is the canonical field-extension class `IsGalois`. -/
#check IsGalois
