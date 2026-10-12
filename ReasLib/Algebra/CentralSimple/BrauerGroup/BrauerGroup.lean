/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.Group
public import ReasLib.Algebra.CentralSimple.BrauerGroup.Degree
public import ReasLib.Algebra.CentralSimple.BrauerGroup.Trivial
public import ReasLib.Algebra.CentralSimple.BrauerGroup.DivisionRepresentative

/-! # Brauer Group

Sub-modules for the Brauer group of a field.

- `Group` — `CommGroup (BrauerGroup k)` instance
- `Degree` — `CSA.degree`, square-dimension theorem
- `Trivial` — Br(k) = 1 for algebraically closed fields
- `DivisionRepresentative` — division algebra representatives of Brauer classes
-/

