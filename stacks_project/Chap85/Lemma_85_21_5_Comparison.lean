/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.Slice

@[expose] public section

universe u v

open CategoryTheory

variable {C : Type u} [Category.{v} C] (U : SimplicialObject C)

#check (CategoryTheory.SimplicialObject.sliceTotalSite U : Type (max u v))
