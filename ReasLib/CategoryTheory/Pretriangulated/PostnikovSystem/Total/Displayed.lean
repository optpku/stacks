module

public import ReasLib.CategoryTheory.DisplayedCategory.Total
public import ReasLib.CategoryTheory.DisplayedCategory.Based.Total
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Displayed
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Forget

/-!
# The displayed-category model of total Postnikov systems

This leaf identifies the specialized total category of finite Postnikov systems with the
generic total category of their displayed-category presentation.  Both comparison functors
retain the stored base and displayed data definitionally; the computation API lets downstream
files use this identification without unfolding either total-category implementation.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem.Total

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]

variable (D) in
/-- Send a specialized total Postnikov system to the generic total object of the displayed
category `PostnikovSystem.Morphism.displayedCategory D n`. -/
@[stacks 0D7Z "specialized-to-displayed total Postnikov-system functor"]
def toDisplayed (n : ℕ) :
    PostnikovSystem.Total D n ⥤
      DisplayedCategory.Total (PostnikovSystem.Morphism.displayedCategory D n) where
  obj P := ⟨P.base, P.system⟩
  map f := ⟨f.base, f.systemMap⟩
  map_id := sorry
  map_comp := sorry

namespace toDisplayed

/-- The forward comparison retains the underlying finite row of an object. -/
@[simp, stacks 0D7Z "base object of the displayed total comparison"]
theorem obj_base (n : ℕ) (P : PostnikovSystem.Total D n) :
    ((toDisplayed D n).obj P).base = P.base := sorry

/-- The displayed object of the forward comparison is the stored Postnikov system. -/
@[simp, stacks 0D7Z "displayed object of the total Postnikov-system comparison"]
theorem obj_obj (n : ℕ) (P : PostnikovSystem.Total D n) :
    ((toDisplayed D n).obj P).obj = P.system := sorry

/-- The forward comparison retains the base component of a morphism. -/
@[simp, stacks 0D7Z "base map of the displayed total comparison"]
theorem map_base {n : ℕ} {P Q : PostnikovSystem.Total D n} (f : P ⟶ Q) :
    ((toDisplayed D n).map f).base = f.base := sorry

/-- The displayed component of the forward comparison is the stored system map. -/
@[simp, stacks 0D7Z "displayed map of the total Postnikov-system comparison"]
theorem map_displayed {n : ℕ} {P Q : PostnikovSystem.Total D n} (f : P ⟶ Q) :
    ((toDisplayed D n).map f).displayed = f.systemMap := sorry

/-- The forward comparison commutes strictly with projection to finite rows. -/
@[stacks 0D7Z "projection formula for the displayed total comparison"]
theorem forget (n : ℕ) :
    toDisplayed D n ⋙
        DisplayedCategory.Total.forget (PostnikovSystem.Morphism.displayedCategory D n) =
      PostnikovSystem.Total.forget D n := sorry

end toDisplayed

variable (D) in
/-- Recover the specialized total Postnikov system from a generic displayed total object. -/
@[stacks 0D7Z "displayed-to-specialized total Postnikov-system functor"]
def ofDisplayed (n : ℕ) :
    DisplayedCategory.Total (PostnikovSystem.Morphism.displayedCategory D n) ⥤
      PostnikovSystem.Total D n where
  obj P := ⟨P.base, P.obj⟩
  map f := ⟨f.base, f.displayed⟩
  map_id := sorry
  map_comp := sorry

namespace ofDisplayed

/-- The reverse comparison retains the underlying finite row of an object. -/
@[simp, stacks 0D7Z "base object of the specialized total comparison"]
theorem obj_base (n : ℕ)
    (P : DisplayedCategory.Total (PostnikovSystem.Morphism.displayedCategory D n)) :
    ((ofDisplayed D n).obj P).base = P.base := sorry

/-- The specialized system recovered by the reverse comparison is the displayed object. -/
@[simp, stacks 0D7Z "Postnikov system of the specialized total comparison"]
theorem obj_system (n : ℕ)
    (P : DisplayedCategory.Total (PostnikovSystem.Morphism.displayedCategory D n)) :
    ((ofDisplayed D n).obj P).system = P.obj := sorry

/-- The reverse comparison retains the base component of a morphism. -/
@[simp, stacks 0D7Z "base map of the specialized total comparison"]
theorem map_base {n : ℕ}
    {P Q : DisplayedCategory.Total (PostnikovSystem.Morphism.displayedCategory D n)}
    (f : P ⟶ Q) : ((ofDisplayed D n).map f).base = f.base := sorry

/-- The specialized system map recovered by the reverse comparison is the displayed map. -/
@[simp, stacks 0D7Z "Postnikov-system map of the specialized total comparison"]
theorem map_systemMap {n : ℕ}
    {P Q : DisplayedCategory.Total (PostnikovSystem.Morphism.displayedCategory D n)}
    (f : P ⟶ Q) : ((ofDisplayed D n).map f).systemMap = f.displayed := sorry

/-- The reverse comparison commutes strictly with projection to finite rows. -/
@[stacks 0D7Z "projection formula for the specialized total comparison"]
theorem forget (n : ℕ) :
    ofDisplayed D n ⋙ PostnikovSystem.Total.forget D n =
      DisplayedCategory.Total.forget
        (PostnikovSystem.Morphism.displayedCategory D n) := sorry

end ofDisplayed

variable (D) in
/-- The explicit strict isomorphism between the specialized and generic total categories of
finite Postnikov systems. -/
@[stacks 0D7Z "strict displayed realization of total Postnikov systems"]
def strictIso (n : ℕ) :
    IsoCat (PostnikovSystem.Total D n)
      (DisplayedCategory.Total (PostnikovSystem.Morphism.displayedCategory D n)) where
  functor := toDisplayed D n
  inverse := ofDisplayed D n
  unit_eq := sorry
  counit_eq := sorry

namespace strictIso

/-- The forward functor of the strict isomorphism is `toDisplayed`. -/
@[simp, stacks 0D7Z "forward functor of the strict displayed realization"]
theorem functor (n : ℕ) : (strictIso D n).functor = toDisplayed D n := sorry

/-- The inverse functor of the strict isomorphism is `ofDisplayed`. -/
@[simp, stacks 0D7Z "inverse functor of the strict displayed realization"]
theorem inverse (n : ℕ) : (strictIso D n).inverse = ofDisplayed D n := sorry

end strictIso

variable (D) in
/-- The category equivalence underlying the strict displayed realization of total Postnikov
systems. -/
@[stacks 0D7Z "displayed realization equivalence for total Postnikov systems"]
def equivalence (n : ℕ) :
    PostnikovSystem.Total D n ≌
      DisplayedCategory.Total (PostnikovSystem.Morphism.displayedCategory D n) :=
  (strictIso D n).toEquivalence

namespace equivalence

/-- The forward functor of the equivalence is the explicit forward comparison. -/
@[simp, stacks 0D7Z "forward functor of the displayed realization equivalence"]
theorem functor (n : ℕ) : (equivalence D n).functor = toDisplayed D n := sorry

/-- The inverse functor of the equivalence is the explicit reverse comparison. -/
@[simp, stacks 0D7Z "inverse functor of the displayed realization equivalence"]
theorem inverse (n : ℕ) : (equivalence D n).inverse = ofDisplayed D n := sorry

end equivalence

variable (D) in
/-- The strict isomorphism over `ComposableArrows D n` induced by the displayed realization.
Its source and target projections are the specialized and generic forgetful functors. -/
@[stacks 0D7Z "strict displayed realization over finite composable rows"]
def basedStrictIso (n : ℕ) :
    BasedCategory.StrictIso
      (BasedCategory.ofFunctor (PostnikovSystem.Total.forget D n))
      (DisplayedCategory.Total.toBased
        (PostnikovSystem.Morphism.displayedCategory D n)) where
  toIsoCat := strictIso D n
  functor_w := sorry

namespace basedStrictIso

/-- The forward based functor has `toDisplayed` as its underlying functor. -/
@[simp, stacks 0D7Z "forward functor of the based strict displayed realization"]
theorem hom_toFunctor (n : ℕ) :
    (basedStrictIso D n).hom.toFunctor = toDisplayed D n := sorry

/-- The inverse based functor has `ofDisplayed` as its underlying functor. -/
@[simp, stacks 0D7Z "inverse functor of the based strict displayed realization"]
theorem inv_toFunctor (n : ℕ) :
    (basedStrictIso D n).inv.toFunctor = ofDisplayed D n := sorry

end basedStrictIso

end CategoryTheory.PostnikovSystem.Total

end
