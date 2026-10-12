/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Module.SupportDim
public import ReasLib.RingTheory.Module.Support.BaseChange
public import ReasLib.RingTheory.Module.Support.Localization
public import ReasLib.RingTheory.Module.Support.RestrictScalars
public import ReasLib.RingTheory.Module.Support.Annihilator
public import ReasLib.RingTheory.Module.Support.Fiber
public import ReasLib.RingTheory.Module.Support.IdealPower

/-!
# Support API for modules

Aggregate import for the reusable module-support owners.  The leaves separate
support dimension, scalar extension, localization, restriction of scalars, and
annihilator quotients so consumers can import only the layer they need.
-/

@[expose] public section
