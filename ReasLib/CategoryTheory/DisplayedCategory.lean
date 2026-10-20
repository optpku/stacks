/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.Structure
public import ReasLib.CategoryTheory.DisplayedCategory.Transport
public import ReasLib.CategoryTheory.DisplayedCategory.Total
public import ReasLib.CategoryTheory.DisplayedCategory.Total.Transport
public import ReasLib.CategoryTheory.DisplayedCategory.Based.Total
public import ReasLib.CategoryTheory.DisplayedCategory.Fiber
public import ReasLib.CategoryTheory.DisplayedCategory.Fiber.Computation
public import ReasLib.CategoryTheory.DisplayedCategory.Fiber.Comparison
public import ReasLib.CategoryTheory.DisplayedCategory.Functor
public import ReasLib.CategoryTheory.DisplayedCategory.Functor.Computation
public import ReasLib.CategoryTheory.DisplayedCategory.Functor.Reindex
public import ReasLib.CategoryTheory.DisplayedCategory.Fiber.Functor
public import ReasLib.CategoryTheory.DisplayedCategory.Fiber.Functor.Category
public import ReasLib.CategoryTheory.DisplayedCategory.NatTrans
public import ReasLib.CategoryTheory.DisplayedCategory.NatTrans.Reindex
public import ReasLib.CategoryTheory.DisplayedCategory.Functor.Category
public import ReasLib.CategoryTheory.DisplayedCategory.NatTrans.Whiskering
public import ReasLib.CategoryTheory.DisplayedCategory.Fiber.NatTrans
public import ReasLib.CategoryTheory.DisplayedCategory.Based

/-!
# Displayed-category support

This is the narrow public entry point for the reusable displayed-category infrastructure.  The
individual leaves keep the dependent structure, equality transport, total category, fibers,
displayed functors, and displayed natural transformations separately importable.
-/
