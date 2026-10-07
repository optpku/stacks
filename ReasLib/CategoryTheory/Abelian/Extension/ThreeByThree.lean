module

public import ReasLib.CategoryTheory.Abelian.Extension.Ext
public import ReasLib.CategoryTheory.Abelian.Extension.PullPush

@[expose] public section

/-!
# Three-by-Three Diagrams of Extensions

This module packages the reusable data relating two composable short exact extensions.  The
right-hand pullback square is the canonical compact owner: in an abelian category it recovers the
usual commutative `3 x 3` diagram with exact rows and columns.
-/

namespace CategoryTheory

universe w v u

open Abelian Limits

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B D : C}

namespace Extension

/-- Exact `3 x 3` data over composable extensions `S` and `T`.

The middle row is an extension of `T.E` by `A`; `middleColumnMap` compares its middle object with
that of `S`.  The left square commutes and the right square is a pullback. -/
@[stacks 0GSM]
structure ThreeByThree (S : Extension A B) (T : Extension B D) where
  /-- The middle short exact row. -/
  middleRow : Extension A T.E
  /-- The map from the middle object of the top row to that of the middle row. -/
  middleColumnMap : S.E ⟶ middleRow.E
  /-- Commutativity of the left square. -/
  left_comm : S.f ≫ middleColumnMap = middleRow.f
  /-- The right square is a pullback. -/
  right_pullback : IsPullback S.g middleColumnMap T.f middleRow.g

namespace ThreeByThree

variable {S : Extension A B} {T : Extension B D}

/-- Commutativity of the right square underlying a three-by-three diagram. -/
@[simp]
theorem right_comm (X : ThreeByThree S T) :
    S.g ≫ T.f = X.middleColumnMap ≫ X.middleRow.g := sorry

/-- The top row of a three-by-three diagram is categorically isomorphic to the pullback of its
middle row. -/
theorem pullback_isIsomorphic (X : ThreeByThree S T) :
    IsIsomorphic (Extension.pullback T.f X.middleRow) S := sorry

/-- A pullback presentation of the top row produces a three-by-three diagram. -/
theorem nonempty_of_isIsomorphic (U : Extension A T.E)
    (h : IsIsomorphic (Extension.pullback T.f U) S) :
    Nonempty (ThreeByThree S T) := sorry

/-- Three-by-three diagrams are equivalently pullback presentations of their top row. -/
theorem nonempty_iff_exists_isIsomorphic :
    Nonempty (ThreeByThree S T) ↔
      ∃ U : Extension A T.E, IsIsomorphic (Extension.pullback T.f U) S := sorry

/-- Three-by-three diagrams are equivalently lifts of the top extension class along `T.f`. -/
theorem nonempty_iff_exists_pullback :
    Nonempty (ThreeByThree S T) ↔
      ∃ U : Extension A T.E,
        ExtensionClass.pullback T.f (⟦U⟧ : ExtensionClass A T.E) =
          (⟦S⟧ : ExtensionClass A B) := sorry

variable [HasExt.{w} C]

/-- The Yoneda product of two composable extension classes vanishes exactly when the extensions
fit into a three-by-three diagram. -/
@[stacks 0GSM]
theorem comp_eq_zero_iff_nonempty :
    T.extClass.comp S.extClass rfl = 0 ↔
      Nonempty (ThreeByThree S T) := sorry

end ThreeByThree

end Extension

end

end CategoryTheory

-- The data owner and its principal construction and classification views.
