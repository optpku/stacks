/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import ReasLib.CategoryTheory.Presheaf.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] (G : Presheaf.{u, v, w} C) (H : Subfunctor G)

/-
Definition 7.3.3: a Type-valued presheaf F is a subpresheaf of G when, for every object U of C,
the set of sections of F at U is a subset of the sections of G at U, compatibly with restriction.
Equivalently, the objectwise inclusions glue to an injective morphism F ⟶ G.

Stacks writes F ⊂ G. Mathlib names this H : Subfunctor G, with H.obj the objectwise subsets,
H.map the restriction compatibility, H.toFunctor the subpresheaf F, and H.ι : H.toFunctor ⟶ G
the inclusion.
-/
@[stacks 00V8] #check (CategoryTheory.Subfunctor G : Type (max u w))

#check H.obj
#check H.map
#check H.toFunctor
#check (H.ι : H.toFunctor ⟶ G)
