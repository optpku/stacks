module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Induced
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LocallyInduced.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LocallyInduced.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LocallyInduced.Bilimit

/-!
# Locally induced pseudopullback compatibility aggregate

This historical import path exports the concrete forgetful cone and pseudofunctor, their
computation API, and the bilimit-transfer criterion. Focused consumers should import
`LocallyInduced.Basic`, `LocallyInduced.Computations`, or `LocallyInduced.Bilimit` according to
the strongest interface they need.
-/
