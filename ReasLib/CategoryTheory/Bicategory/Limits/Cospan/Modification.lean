/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Computations

/-!
# Modifications of bicategorical cospans

Compatibility aggregate for the generator-level modification API between strong
walking-cospan transformations. Focused consumers should import `Modification.Basic`,
`Modification.Construction`, or `Modification.Computations` according to the layer they use.

The modification data are three vertex `2`-cells and one naturality equation for each generating
arrow; the finite walking-cospan assembly and its computation API are kept in separate owners.
-/
