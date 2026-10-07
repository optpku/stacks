module

public import Mathlib.CategoryTheory.Category.Basic
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {W X Y Z : C}
variable (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)

/- Domain-style sampling for Definition 4.2.1:
- primary domain: the primitive data and axioms of a category.
- inspected owner declarations: `Quiver.Hom`, `CategoryStruct.id`, `CategoryStruct.comp`,
  and `Category`.
- best owner abstraction: `Category`; its inherited owner stack already carries the textbook data,
  so this file should recall that owner instead of introducing a parallel wrapper.

Primitive-vs-derived split:
- primitive data inherited by the owner stack: hom-types from `Quiver.Hom`, identity morphisms
  from `CategoryStruct.id`, composition from `CategoryStruct.comp`, and the axioms from
  `Category`.
- derived API used on the source-facing surface: the standard notation `X ⟶ Y`, `𝟙 X`, `f ≫ g`,
  together with `Category.id_comp`, `Category.comp_id`, and `Category.assoc`.

Source/core/bridge triage:
- `source-facing`: the textbook hom-set, identity, composition, and three category axioms.
- `core/canonical`: `Category`.
- `bridge/view`: the inherited notation and axiom names exposing the source wording on top of the
  canonical owner stack. -/

/- Definition 4.2.1: a category on the ambient type of objects `C` is the canonical mathlib class
`Category`. The source hom-types, identities, and composition are already the inherited data
`Quiver.Hom`, `CategoryStruct.id`, and `CategoryStruct.comp`, so no parallel local definition is
needed. The left/right identity axioms and associativity are the fields of `Category` itself. -/
@[stacks 0014 "category structure"]
#check (Category.{v} C : Type max u (v + 1))

/- Definition 4.2.1, source hom-set notation: for objects `X Y : C`, the morphisms from `X` to
`Y` form the canonical hom-type `X ⟶ Y`, i.e. the notation for `Quiver.Hom X Y`. -/
@[stacks 0014 "morphism types"] #check (X ⟶ Y)

/- Definition 4.2.1, source identity morphism: the identity of an object `X` is the canonical
morphism `𝟙 X`, i.e. the notation for `CategoryStruct.id X`. -/
@[stacks 0014 "identity morphism"] #check (𝟙 X)

/- Definition 4.2.1, source composition operation: composition of composable morphisms is the
canonical infix operation `≫`, i.e. the notation for `CategoryStruct.comp`. -/
@[stacks 0014 "composition"] #check fun (g : Y ⟶ Z) (f : X ⟶ Y) ↦ f ≫ g

/- Definition 4.2.1 (1): in source order, `id_x ∘ φ = φ` is the canonical arrows-convention
axiom `Category.comp_id`. -/
@[stacks 0014 "identity after a morphism"]
#check (Category.comp_id f : f ≫ 𝟙 Y = f)

/- Definition 4.2.1 (2): in source order, `ψ ∘ id_x = ψ` is the canonical arrows-convention
axiom `Category.id_comp`. -/
@[stacks 0014 "morphism after an identity"]
#check (Category.id_comp f : 𝟙 X ≫ f = f)

/- Definition 4.2.1 (3): associativity of composition is the canonical axiom
`Category.assoc`. -/
@[stacks 0014 "associativity law"]
#check (Category.assoc f g h : (f ≫ g) ≫ h = f ≫ g ≫ h)

end CategoryTheory
