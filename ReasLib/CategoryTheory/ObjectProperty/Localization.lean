/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.Localization.FullSubcategory
public import ReasLib.CategoryTheory.ObjectProperty.Localization.FullSubcategory.Monotonicity
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Resolution
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Comparison
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Calculus
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Saturation
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Equivalence
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Kernel
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Factorization

/-!
# Localizing Full Subcategories

Convenience import for the basic, resolution, saturation, equivalence, triangulated, and
Verdier-quotient APIs for localizing a full subcategory.  Each result lives in its smallest
dependency leaf.
-/
