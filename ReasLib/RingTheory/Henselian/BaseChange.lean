/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.Henselization.BaseChange.AtPrime.QuasiFinite
public import ReasLib.RingTheory.Henselian.Henselization.Quotient
public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.AtPrime.QuasiFinite
public import ReasLib.RingTheory.Henselian.StrictHenselization.Quotient
public import ReasLib.RingTheory.Algebra.TensorProduct.Locality
public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.AtPrime.TensorProduct.CommonField
public import ReasLib.RingTheory.Localization.AtPrime.TensorProduct.CommonField.TensorMap

/-!
# Henselian base-change and tensor-product APIs

This aggregate is the heavy companion to `ReasLib.RingTheory.Henselian`.  It
collects the reusable prime-local base-change, quotient, tensor-locality, and
strict-henselization tensor-comparison owners used by later chapters.  The
leaves remain independent of this file, so importing one specialized result
does not pull the whole base-change stack into a small development.

@stack 05WP
@stack 05WQ
@stack 05WR
@stack 05WS
@stack 092Y
@stack 0GIP
-/

@[expose] public section
