/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Nerve

/-!
# Groupoid-scheme nerve

The nerve construction is owned by the shared groupoid-scheme library.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.GroupoidScheme.simplicialScheme :
    {S : Scheme.{u}} → GroupoidScheme S → SimplicialObject Scheme.{u})
