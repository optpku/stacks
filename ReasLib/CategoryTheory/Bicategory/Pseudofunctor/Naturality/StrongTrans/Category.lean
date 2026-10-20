/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit hom-categories for strong transformations

The mathlib category structure on `Pseudofunctor.StrongTrans` is intentionally scoped.  In
heterogeneous universe contexts, typeclass search can leave the universe of its underlying
`CategoryStruct` unresolved even after the scope is opened.  This leaf provides the same
canonical structure with the endpoints explicit in the expected type, so downstream constructions
can use one stable instance without repeating local pins.
-/

@[expose] public section

namespace CategoryTheory

universe wB vB uB wC vC uC

namespace Pseudofunctor.StrongTrans

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

/-- The canonical category structure on pseudofunctors, whose morphisms are strong
transformations. -/
scoped instance categoryStructOwner :
    CategoryStruct (Pseudofunctor B C) :=
  CategoryTheory.Pseudofunctor.StrongTrans.categoryStruct

/-- The canonical modification category on strong transformations, with the endpoint
pseudofunctors fixed by the expected `StrongTrans F G` type. -/
scoped instance homCategoryOwner {F G : Pseudofunctor B C} :
    Category (StrongTrans F G) :=
  CategoryTheory.Pseudofunctor.StrongTrans.homCategory

end Pseudofunctor.StrongTrans

end CategoryTheory
