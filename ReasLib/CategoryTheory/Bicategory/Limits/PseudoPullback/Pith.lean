module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Pith.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Pith.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Pith.Symmetry

/-!
# Pseudopullback cones in the pith

This compatibility import assembles the explicit pith-valued cone and preservation of its
bilimit property, together with the data-level compatibility of pith restriction and symmetry.
Data-only consumers should import `Pith.Basic` or `Pith.Symmetry`; universal-property consumers
should import `Pith.Bilimit`.
-/
