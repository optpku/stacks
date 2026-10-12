/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Computations

/-!
# Morphisms of bicategorical cospans

This is the compatibility aggregate for the generator-level API of strong transformations
between walking-cospan pseudodiagrams. Focused consumers should import `Hom.Basic`,
`Hom.Construction`, or `Hom.Computations` according to the data they use.
-/
