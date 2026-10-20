/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.PithStrict
public import ReasLib.CategoryTheory.Bicategory.GroupoidHom
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.LocalProperties
import StacksCheckRecall

@[expose] public section

universe w u v

namespace CategoryTheory

open Bicategory

variable (B : Type u) [Bicategory.{w, v} B]

/-
Remark 4.30.3 separates one generic construction from examples that already realize it. For any
bicategory `B`, `Pith B` keeps its objects and `1`-morphisms and retains only invertible
`2`-morphisms.

When an owner is already locally groupoidal, its direct owner is the canonical `(2,1)` surface;
applying `Pith` would add a carrier wrapper without changing the mathematics. This applies to the
groupoid example below; fibred and stack owners are introduced later.

The previous version imported the later stack chapter solely to name `StackInGroupoidsOver`.
That reverses the source dependency and makes this elementary remark compile all later stack
proofs. Stacks are instead recorded here through the generic rule: once the later chapter
introduces `StackOver J`, its `(2, 1)` variant is `Pith (StackOver J)`. The same construction
continues to every other bicategorical owner, which is precisely the source's “and so on.”

Import decision: `CategoryTheory.Bicategory.PithStrict` and
`CategoryTheory.Bicategory.GroupoidHom` expose the two generic instances used by this item;
`CategoryTheory.Bicategory.InducedBicategory.LocalProperties` supplies the induced groupoid
bicategory instance. `StacksCheckRecall` remains plain because it only elaborates the annotations
below.
-/

/- Remark 4.30.3: `Pith` is the generic `(2,1)` construction; groupoid-valued examples that
already have only invertible `2`-morphisms use their direct canonical owners below. -/
@[stacks 003M "canonical (2,1)-variant"]
#check (Pith B : Type u)

/- The canonical full-object bicategory of groupoids induced from `Cat` is itself locally
groupoidal; no `Pith` carrier is needed. -/
@[stacks 003M "(2,1)-category of groupoids"]
#check (inferInstance :
  IsLocallyGroupoid (InducedBicategory Cat.{v, u} Grpd.forgetToCat.obj))

end CategoryTheory
