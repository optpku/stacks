/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.Essential
import StacksCheckRecall

open CategoryTheory

universe u v

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {X Y : 𝒜} (A : CategoryTheory.Subobject X) (f : X ⟶ Y)

/- Definition 47.2.1 (1): A subobject is essential when its intersection with every
nonzero subobject is nonzero. -/
@[stacks 08XJ] #check (CategoryTheory.Subobject.IsEssential A : Prop)

/- Definition 47.2.1 (2): An epimorphism is essential when no proper subobject of its
source maps onto its target. -/
@[stacks 08XJ] #check (CategoryTheory.IsEssentialEpi f : Prop)
