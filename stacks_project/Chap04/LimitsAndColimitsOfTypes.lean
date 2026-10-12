/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import StacksCheckRecall

@[expose] public section

/-!
# Limits and colimits of types

This file records the canonical mathlib realization of Categories, Section 4.15
(tag `002U`). The source section has no numbered declaration: it describes limits of
type-valued diagrams as compatible families and colimits as a quotient of the dependent
sum of their values.

No project-specific `Type`-valued limit or colimit is introduced here. In particular, the
abstract categorical objects are related to the concrete models by equivalences rather than
by exposing the universe-sensitive internal `TypeMax` implementations as definitional equalities.
-/

namespace CategoryTheory

open Limits

universe v u w

section Limits

variable [UnivLE.{v, u}]

/- Section 4.15 (tag `002U`), limit half: `Type u` has all appropriately small limits.
For `F : J ⥤ Type u`, `F.sections` is the subtype of families `x : ∀ j, F.obj j`
satisfying `F.map f (x j) = x j₂` for every `f : j ⟶ j₂`. The equivalence
`Limits.Types.limitEquivSections F` identifies this concrete compatible-family model with
the abstract categorical limit. `Limits.Types.Limit.mk` and `Limits.Types.limit_ext` are
the corresponding constructor and extensionality API. -/

@[stacks 002U "types have all appropriately small limits"]
#check (Limits.Types.hasLimitsOfSize.{v, u, w} :
  HasLimitsOfSize.{w, v, u, u + 1} (Type u))

end Limits

section LimitModel

variable {J : Type u} [Category.{v} J] (F : J ⥤ Type w)

@[stacks 002U "compatible families of a type-valued diagram"]
#check (Functor.sections F : Set (∀ j, F.obj j))

variable [HasLimit F]

@[stacks 002U "abstract limit identified with compatible families"]
#check (Limits.Types.limitEquivSections F : limit F ≃ F.sections)

@[stacks 002U "construct an abstract limit element from a compatible family"]
#check (Limits.Types.Limit.mk F :
  (x : ∀ j, F.obj j) →
    (∀ (j j' : J) (f : j ⟶ j'), F.map f (x j) = x j') → limit F)

@[stacks 002U "extensionality of elements of a type-valued limit"]
#check (Limits.Types.limit_ext F :
  ∀ x y : limit F, (∀ j, limit.π F j x = limit.π F j y) → x = y)

end LimitModel

section Colimits

variable [UnivLE.{v, u}]

/- Section 4.15 (tag `002U`), colimit half: `Type u` has all appropriately small colimits.
For `F : J ⥤ Type u`, `F.ColimitTypeRel` records one forward identification along a morphism,
and `F.ColimitType` is `Quot F.ColimitTypeRel` on `Σ j, F.obj j`. Equality of canonical
representatives is characterized by `Relation.EqvGen F.ColimitTypeRel`, which is the generated
equivalence relation represented in the source by an alternating zigzag. The canonical maps,
joint surjectivity, and the quotient eliminator are exposed directly; the equivalence
`Limits.Types.colimitEquivColimitType F` identifies this quotient with the abstract colimit. -/

@[stacks 002U "types have all appropriately small colimits"]
#check (Limits.Types.hasColimitsOfSize.{v, u, w} :
  HasColimitsOfSize.{w, v, u, u + 1} (Type u))

end Colimits

section ColimitModel

variable {J : Type u} [Category.{v} J] (F : J ⥤ Type w)

@[stacks 002U "generating relation for the concrete colimit quotient"]
#check (Functor.ColimitTypeRel F :
  (Σ j, F.obj j) → (Σ j, F.obj j) → Prop)

@[stacks 002U "concrete colimit as a quotient of the dependent sum"]
#check (Functor.ColimitType F : Type (max u w))

@[stacks 002U "canonical representatives in the concrete colimit"]
#check (Functor.ιColimitType F : ∀ j, F.obj j → F.ColimitType)

@[stacks 002U "equality of representatives via the generated equivalence relation"]
#check (Functor.ιColimitType_eq_iff F :
  ∀ {j j' : J} (x : F.obj j) (y : F.obj j'),
    F.ιColimitType j x = F.ιColimitType j' y ↔
      Relation.EqvGen F.ColimitTypeRel ⟨j, x⟩ ⟨j', y⟩)

@[stacks 002U "every concrete colimit element has a component representative"]
#check (Functor.ιColimitType_jointly_surjective F :
  ∀ t : F.ColimitType, ∃ j x, F.ιColimitType j x = t)

@[stacks 002U "identification of a representative with its image along a diagram morphism"]
#check (Functor.ιColimitType_map F :
  ∀ {j j' : J} (f : j ⟶ j') (x : F.obj j),
    F.ιColimitType j' (F.map f x) = F.ιColimitType j x)

@[stacks 002U "quotient eliminator for the concrete colimit"]
#check (Functor.descColimitType F :
  ∀ c : F.CoconeTypes, F.ColimitType → c.pt)

variable [HasColimit F]

@[stacks 002U "abstract colimit identified with the concrete quotient"]
#check (Limits.Types.colimitEquivColimitType F : colimit F ≃ F.ColimitType)

end ColimitModel

end CategoryTheory
