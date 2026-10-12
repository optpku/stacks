/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Domain sampling:
- Primary domain: monoidal category theory.
- Core/canonical declarations inspected:
  - `CategoryTheory.MonoidalCategory`
  - `CategoryTheory.MonoidalCategoryStruct`
  - `MonoidalCategory.associatorNatIso`
  - `MonoidalCategory.leftUnitorNatIso`
- Owner abstraction: `CategoryTheory.MonoidalCategory`.
- Layer triage:
  - `source-facing`: Definition 4.43.1 is a recall-only item for the standard notion of a
    monoidal category, with no extra source-defined data beyond the ambient owner;
  - `core/canonical`: `MonoidalCategory`, which is the bundled owner of the tensor product,
    tensor unit, associator, unitors, and coherence axioms;
  - `bridge/view`: none needed here; `MonoidalCategoryStruct` is only the auxiliary raw-data
    layer that `MonoidalCategory` extends.
- Primitive vs. derived:
  - primitive data: tensor product on objects and morphisms, whiskering, tensor unit,
    associator, left unitor, right unitor, and the coherence axioms stored by
    `MonoidalCategory`;
  - derived API: the functorial tensor constructions and the natural-isomorphism packaging
    `associatorNatIso`, `leftUnitorNatIso`, and `rightUnitorNatIso`.
-/

/- Definition 4.43.1: the Stacks notion of a monoidal category is the canonical mathlib owner
`CategoryTheory.MonoidalCategory`. The auxiliary `MonoidalCategoryStruct` isolates only the raw
data layer, so the public chapter API should recall the bundled owner directly. -/
@[stacks 0FFK "monoidal category with tensor, associator, coherent unit, and coherence laws"]
#check (MonoidalCategory C : Type (max u v))

end CategoryTheory
