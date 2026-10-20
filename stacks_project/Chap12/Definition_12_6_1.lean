/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.Extension.Basic
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (A B : C)

/- Definition 12.6.1 [010J] (1): an extension of `B` by `A` is a
fixed-endpoint short exact sequence. -/
@[stacks 010J]
#check (Extension A B : Type _)

variable (S T : Extension A B)

/- Definition 12.6.1 [010J] (2): a morphism of extensions is an
endpoint-preserving morphism of their middle objects. -/
@[stacks 010J]
#check (Extension.Hom S T : Type _)

/- Definition 12.6.1 [010J] (3): fixed-endpoint extensions form a category. -/
@[stacks 010J]
#check (inferInstance : Category (Extension A B))

#check (Extension.toShortComplexFunctor (A := A) (B := B) :
  Extension A B ⥤ ShortComplex C)
#check (inferInstance :
  (Extension.toShortComplexFunctor (A := A) (B := B)).Faithful)

end CategoryTheory
