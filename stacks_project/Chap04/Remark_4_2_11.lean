/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Small
import StacksCheckRecall

@[expose] public section


universe u v w

namespace CategoryTheory
namespace ObjectProperty

variable {A : Type u} [Category.{v} A]
variable (F : A ⥤ Type w)

/-
The source needs the literal objectwise range and a concrete factorization through its full
subcategory. `ObjectProperty.ofObj`, `ObjectProperty.lift`, `ObjectProperty.liftCompιIso`, and the
`ObjectProperty.Small` instance for `ofObj` provide these directly; `Functor.essImage` and
`Functor.toEssImage` would instead close the range under isomorphism. We therefore use
`ofObj F.obj`, with the book's set-sizedness rendered only as universe-relative `Small.{u}` at the
universe of `A`. This keeps the lifted functor explicit and gives downstream code the canonical
comparison with `F` without introducing witness choices.
-/

/- Remark 4.2.11 (1): although `Type w` is large, the literal objectwise range of a set-valued
functor `F : A ⥤ Type w` is small relative to the universe containing the objects of `A`. -/
@[stacks 001E "set-sized objectwise range"]
#check (inferInstance : ObjectProperty.Small.{u} (ofObj F.obj))

/- Remark 4.2.11 (2): the functor `F` canonically lands in the full subcategory of `Type w` whose
objects belong to its literal objectwise range. -/
@[stacks 001E "factorization through the full subcategory on the objectwise range"]
#check ((ofObj F.obj).lift F (ofObj_apply F.obj) :
  A ⥤ (ofObj F.obj).FullSubcategory)

/- The canonical inclusion of the range full subcategory recovers `F`. -/
#check (ofObj F.obj).liftCompιIso F (ofObj_apply F.obj)

/- The resulting full subcategory is itself small relative to the universe of `A`. -/
#check (inferInstance : _root_.Small.{u} (ofObj F.obj).FullSubcategory)

end ObjectProperty
end CategoryTheory
