/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Basic
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Universal.Lift
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Universal.Lift.Functoriality
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Universal.Equivalence

/-!
# Universal colax costructured arrows

This is the focused entry point for the representation-independent universal-object API of a
colax costructured-arrow bicategory. It exposes the universal predicate, chosen lifts and their
specifications, identity and composition coherence, and the equivalence between two universal
source objects.

Shape-specific notions such as conical bilimits should specialize this layer and retain only
readable component formulas of their own.
-/
