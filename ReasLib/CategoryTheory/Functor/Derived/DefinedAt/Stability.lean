module

public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic

/-!
# Stability of source-defined derived values

Source-definedness is inherited from terminal or initial localization denominators, transported
along localized morphisms and isomorphisms, and automatic for functors that invert the localized
class. These statements concern only the essentially constant diagram, not a selected
presentation.
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']

/-- A terminal object of the right-derived indexing category gives an essentially constant
presentation, hence source-definedness at `X`. -/
theorem RightDerived.DefinedAt.of_isTerminal
    (F : D ⥤ D') (S : MorphismProperty D) (X : D)
    {d : CostructuredArrow S.Q (S.Q.obj X)} (hd : IsTerminal d) :
    RightDerived.DefinedAt F S X := sorry

/-- An initial object of the left-derived indexing category gives an essentially constant
presentation, hence source-definedness at `X`. -/
theorem LeftDerived.DefinedAt.of_isInitial
    (F : D ⥤ D') (S : MorphismProperty D) (X : D)
    {d : StructuredArrow (S.Q.obj X) S.Q} (hd : IsInitial d) :
    LeftDerived.DefinedAt F S X := sorry

/-- Source-definedness of a right-derived value is invariant along a morphism belonging to the
localized class. -/
theorem RightDerived.DefinedAt.iff_of_mem
    (F : D ⥤ D') (S : MorphismProperty D) {X Y : D}
    (f : X ⟶ Y) (hf : S f) :
    RightDerived.DefinedAt F S X ↔ RightDerived.DefinedAt F S Y := sorry

/-- Source-definedness of a left-derived value is invariant along a morphism belonging to the
localized class. -/
theorem LeftDerived.DefinedAt.iff_of_mem
    (F : D ⥤ D') (S : MorphismProperty D) {X Y : D}
    (f : X ⟶ Y) (hf : S f) :
    LeftDerived.DefinedAt F S X ↔ LeftDerived.DefinedAt F S Y := sorry

/-- Source-definedness of a right-derived value is stable under isomorphism of the source
object. -/
theorem RightDerived.DefinedAt.of_iso
    (F : D ⥤ D') (S : MorphismProperty D) {X Y : D}
    [RightDerived.DefinedAt F S X] (e : X ≅ Y) :
    RightDerived.DefinedAt F S Y := sorry

/-- Source-definedness of a left-derived value is stable under isomorphism of the source
object. -/
theorem LeftDerived.DefinedAt.of_iso
    (F : D ⥤ D') (S : MorphismProperty D) {X Y : D}
    [LeftDerived.DefinedAt F S X] (e : X ≅ Y) :
    LeftDerived.DefinedAt F S Y := sorry

/-- A functor which inverts `S` has an essentially constant right-derived indexing diagram at
every object. -/
theorem RightDerived.DefinedAt.of_isInvertedBy
    (F : D ⥤ D') (S : MorphismProperty D) (X : D)
    (hF : S.IsInvertedBy F) :
    RightDerived.DefinedAt F S X := sorry

/-- A functor which inverts `S` has an essentially constant left-derived indexing diagram at
every object. -/
theorem LeftDerived.DefinedAt.of_isInvertedBy
    (F : D ⥤ D') (S : MorphismProperty D) (X : D)
    (hF : S.IsInvertedBy F) :
    LeftDerived.DefinedAt F S X := sorry


end CategoryTheory.Functor
