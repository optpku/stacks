/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Equiv
public import ReasLib.RingTheory.Henselian.StrictHenselian
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.Henselization.Comparison
public import ReasLib.RingTheory.Henselian.Henselization.ResidueField
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.Henselian.StrictHenselization.Comparison
public import ReasLib.RingTheory.Henselian.StrictHenselization.Composition
public import ReasLib.RingTheory.Henselian.StrictHenselization.ResidueField
public import ReasLib.RingTheory.Henselian.StrictHenselization.ResidueCoordinate

/-!
# Henselian Local Rings and Henselizations

@stack 04GN
@stack 04GP

Aggregate import for the intrinsic henselian, henselization, and strict-
henselization owners together with their residue-field and comparison APIs.
Categorical presentations and base-change constructions remain opt-in leaves:
they have genuinely heavier dependencies and are not needed to use the
owner-level universal properties.
-/

@[expose] public section
