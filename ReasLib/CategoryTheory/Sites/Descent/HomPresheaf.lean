/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Basic
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.BaseChange
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Composition
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Endpoint.Actions
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Endpoint.Conjugation
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Endpoint.Functoriality
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Isom
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.StrongTrans

/-!
# Canonical Hom-presheaf API

Compatibility aggregate for the canonical Hom-presheaf support API. New
consumers should import the smallest relevant leaf: `Basic`, endpoint
`Actions` or `Conjugation`, `BaseChange`, `Composition`, endpoint
`Functoriality`, `Isom`, or `StrongTrans`.
-/
