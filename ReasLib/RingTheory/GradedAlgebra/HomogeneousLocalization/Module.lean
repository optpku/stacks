/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Module.Basic
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Away.Module

/-!
# Homogeneous-localization module facade

This intentionally small facade is the direct import for consumers that need both the generic
degree-zero localized-module construction and its powers-of-one-element presentation.  Consumers
that need only one layer should import `Module.Basic` or `Away.Module` directly; algebra-side
chart data belongs to the separate `Algebra` and `Chart` leaves.
-/
@[expose] public section

