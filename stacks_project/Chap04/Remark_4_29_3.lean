/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.GroupoidHom
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.LocalProperties
public import ReasLib.CategoryTheory.Bicategory.PithStrict
import StacksCheckRecall

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

/-
Remark 4.29.3 (Stacks tag `003J`) is a universe convention, not a request for a
`BigTwoCategory` wrapper. Lean represents each source-level proper class by a
universe-polymorphic owner type. For `[Bicategory.{w, v} B]`, the object carrier may be large,
while every hom-category `X ⟶ Y` has its objects in `Type v` and its morphisms in `Type w`.

The source's whitelist is retained verbatim at the owner level:
* categories and their `(2,1)` variant;
* groupoids, already a `(2,1)`-category;
* fibred categories over a fixed category and their `(2,1)` variant;
* categories fibred in groupoids, already a `(2,1)`-category;
* stacks over a fixed site and their `(2,1)` variant;
* stacks in groupoids, stacks in setoids, and algebraic stacks over a fixed scheme, each already
  a `(2,1)`-category in the source.

At this dependency layer, `Cat`, `Pith`, and the induced bicategory of groupoids are the available
canonical owners. The fibred and stack owners are introduced later and are therefore recorded
here as part of the convention rather than pulled backwards through imports. Once an ambient
bicategory `B` is available, its generic `(2,1)` variant is `Pith B`; an owner already known to be
locally groupoidal should be used directly, since `Pith` would add a carrier wrapper without
changing the mathematics.

Import decision: `CategoryTheory.Bicategory.GroupoidHom` publicly owns the generic fact that functor
categories into groupoids are groupoids.
`CategoryTheory.Bicategory.InducedBicategory.LocalProperties` is public because its pointwise
groupoid instance supplies the labeled induced-bicategory example below.
`StacksCheckRecall` remains plain because it only elaborates the source annotations.
-/

variable {B : Type u} [Bicategory.{w, v} B] {X Y : B}

/- Remark 4.29.3: universe-polymorphic bicategories encode the source's locally small
hom-categories without an additional size package. -/
@[stacks 003J "locally small hom-categories"]
#check (inferInstance : Category (X ⟶ Y))

/- The first canonical large strict `2`-category in the source's whitelist is `Cat`. -/
@[stacks 003J "large strict 2-category convention"]
#check (Cat.{v, u} : Type (max (u + 1) (v + 1)))

@[stacks 003J "strict 2-category of categories"]
#check (inferInstance : Strict Cat.{v, u})

@[stacks 003J "strictness of the (2,1)-category of categories"]
#check (inferInstance : Strict (Pith Cat.{v, u}))

/- The canonical `(2,1)` variant retains the objects and functors of `Cat` and replaces each
hom-category by its core. No item-specific category-of-natural-isomorphisms wrapper is needed. -/
@[stacks 003J "(2,1)-category of categories"]
#check (inferInstance : IsLocallyGroupoid (Pith Cat.{v, u}))


/- The strict `2`-category of groupoids is the full-object bicategory induced inside `Cat` by
the canonical forgetful object map. Its `1`- and `2`-morphisms remain functors and natural
transformations, rather than a second project-local wrapper. -/
@[stacks 003J "2-category of groupoids"]
#check (InducedBicategory Cat.{v, u} Grpd.forgetToCat.obj :
  Type (max (u + 1) (v + 1)))

@[stacks 003J "strictness of the 2-category of groupoids"]
#check (inferInstance : Strict (InducedBicategory Cat.{v, u} Grpd.forgetToCat.obj))

/- Unlike the generic `Pith` construction, this checks the source's stronger statement that the
groupoid owner itself is locally groupoidal: natural transformations into a groupoid are already
pointwise invertible. -/
@[stacks 003J "(2,1)-category of groupoids"]
#check (inferInstance :
  IsLocallyGroupoid (InducedBicategory Cat.{v, u} Grpd.forgetToCat.obj))

end CategoryTheory
