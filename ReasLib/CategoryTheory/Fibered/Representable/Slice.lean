/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

-- The concrete canonical slice models are owned by the neutral data layer.
public import ReasLib.CategoryTheory.Fibered.InSets.Slice
import Mathlib.Tactic.CrossRefAttribute

/-!
# Representable categories fibred in groupoids

The equivalence-invariant property of being represented by a canonical slice fibration in the
ordinary fixed bicategory.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

/-
Abstraction choice for ordinary representability:

The property is equivalence-invariant object data, not a structure whose witness should be found
by typeclass search. Accordingly `IsRepresentable` is a direct `ObjectProperty` on the ordinary
fixed bicategory `FiberedCategoryOver.Groupoids C`, defined using the canonical bicategorical
equivalence `X ≌ slice U`.

`IsRepresentable.eq_equivalenceClosure` identifies this property with the equivalence closure of
the family `U ↦ slice U`. Thus the generic `ObjectProperty.IsClosedUnderEquivalences` API, rather
than a parallel specialized transport lemma, owns invariance under bicategorical equivalence.
Universe-resized and heterogeneous presentations live in the narrow `Lifted` and `OverBase`
companions.
-/

/-- A category fibred in groupoids over `C` is representable when it is equivalent to the
canonical slice `slice U` for some `U : C` in the fixed bicategory
`FiberedCategoryOver.Groupoids C`.

The UpperCamelCase name follows the established `Functor.IsRepresentable` property vocabulary; it
does not signal a typeclass. -/
@[stacks 0046 "representable categories fibred in groupoids"]
def IsRepresentable :
    ObjectProperty (FiberedCategoryOver.Groupoids C) :=
  fun X ↦
    ∃ U : C, Nonempty (X ≌ slice U)

/-- A bicategorical equivalence to a canonical slice fibration directly exhibits ordinary
representability. This constructor avoids exposing the existential packaging of
`IsRepresentable` at applications that already retain the equivalence data. -/
theorem IsRepresentable.ofEquivalence
    {X : FiberedCategoryOver.Groupoids C} {U : C}
    (e : X ≌ slice U) :
    X.IsRepresentable := sorry

/-- A category fibred in groupoids `X` over `C` is representable exactly when there are `U : C`
and an equivalence `X ≌ slice U` in the fixed owner bicategory. -/
theorem IsRepresentable.iff_exists_equivalence
    (X : FiberedCategoryOver.Groupoids C) :
    X.IsRepresentable ↔
      ∃ U : C, Nonempty (X ≌ slice U) := sorry
/- Proof strategy: unfold `IsRepresentable`. -/

/-- Eliminate ordinary representability into a representing object and an equivalence to its
canonical slice fibration. This avoids manually rewriting the defining object property. -/
theorem IsRepresentable.exists_equivalence
    {X : FiberedCategoryOver.Groupoids C} (hX : X.IsRepresentable) :
    ∃ U : C, Nonempty (X ≌ slice U) := sorry
/- Proof strategy: apply the forward direction of `IsRepresentable.iff_exists_equivalence X`. -/

/-- In the fixed bicategory, representable objects are exactly the equivalence closure of the
family of canonical slice fibrations. -/
theorem IsRepresentable.eq_equivalenceClosure :
    (IsRepresentable (C := C) :
      ObjectProperty (FiberedCategoryOver.Groupoids C)) =
      (ObjectProperty.ofObj
        (fun U : C ↦ slice U)).equivalenceClosure := sorry
/- Proof strategy: extensionality in `X`, use `IsRepresentable.iff_exists_equivalence`, and expand
`ObjectProperty.prop_equivalenceClosure_iff` together with `ObjectProperty.ofObj_iff`; eliminate
the strict equality identifying the image object with `slice U`. -/

/-- Representability is closed under bicategorical equivalence in the ordinary fixed owner. -/
instance IsRepresentable.isClosedUnderEquivalences :
    (IsRepresentable (C := C) :
      ObjectProperty
        (FiberedCategoryOver.Groupoids C)).IsClosedUnderEquivalences := sorry
/- Proof strategy: use `IsRepresentable.eq_equivalenceClosure` and the generic closure instance,
or compose the witnessing equivalence with the supplied bicategorical equivalence. -/

/-- Every ordinary canonical slice fibration is representable in the smallest owner. -/
theorem slice.isRepresentable (U : C) : (slice U).IsRepresentable := sorry
/- Proof strategy: apply `IsRepresentable.iff_exists_equivalence` with representing object `U`
and the identity bicategorical equivalence of `slice U`. -/

end FiberedCategoryOver.Groupoids

end CategoryTheory
