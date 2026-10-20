/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Modification
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Functoriality

/-!
# Mapping bicategorical cospans

Compatibility aggregate for the componentwise cospan mapping API.  The four focused owners follow
the walking-cospan `1`/`2`-cell presentation of Stacks Tag 003O:

* `Map.Basic` owns the concrete transformation (`1`-cell) action;
* `Map.Computations` owns its five generator-level readouts;
* `Map.Modification` owns the componentwise modification (`2`-cell) action and its laws;
* `Map.Functoriality` assembles the induced hom-category functor and isomorphism action.

Existing users may continue importing this path; focused consumers should import the smallest
owner matching the data they use.
-/
