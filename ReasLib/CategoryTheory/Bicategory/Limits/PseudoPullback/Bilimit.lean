/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift.Functoriality
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Equivalence

/-!
# Bilimit pseudopullback squares

This stable aggregate exposes the readable walking-cospan specialization of conical bilimits.
Focused consumers should import `Basic`, `Lift`, `Lift.Functoriality`, or `Equivalence` according
to the strongest universal data they use.
-/
