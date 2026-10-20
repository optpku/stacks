/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Equivalence.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Equivalence.Components
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Equivalence.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Equivalence.Computations

/-!
# Equivalences of bicategorical cospans

Compatibility aggregate for the neutral walking-cospan equivalence API.  Focused consumers can
import `Equivalence.Basic`, `Equivalence.Components`, `Equivalence.Construction`, or
`Equivalence.Computations` according to the layer they use.

The API follows the cospan universal-property pattern: vertex equivalences and the two generating
comparison cells are the complete non-`Prop` input, while inverse naturality and coherence are
obtained from the generic mate construction.
-/
