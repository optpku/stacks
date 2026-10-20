module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Basic
public import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!
# Forgetful Functor from Total Postnikov Systems

This leaf owns the projection from the total category of finite Postnikov
systems to its underlying finite rows.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Total

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]
variable {n : ℕ}

variable (D) in
/-- Forget the Postnikov system while retaining its underlying finite row. -/
@[stacks 0D7Z "forgetful functor from finite Postnikov systems"]
def forget (n : ℕ) : Total D n ⥤ ComposableArrows D n where
  obj P := P.base
  map f := f.base
  map_id P := id_base P
  map_comp f g := comp_base f g

/-- The forgetful functor sends a total object to its underlying finite row. -/
@[simp, stacks 0D7Z]
theorem forget_obj (P : Total D n) : (forget D n).obj P = P.base := sorry

/-- The forgetful functor sends a total morphism to its base component. -/
@[simp, stacks 0D7Z]
theorem forget_map {P Q : Total D n} (f : P ⟶ Q) :
    (forget D n).map f = f.base := sorry

/-! The forgetful functor is the canonical displayed projection of a total Postnikov system.  Its
hom-lift certificates live here, so importing `Total.Forget` is sufficient for ordinary downstream
constructions. -/

/-- Every total Postnikov-system morphism is canonically a hom-lift over its base arrow. -/
@[stacks 0D7Z "hom-lift instance for the total Postnikov-system projection"]
instance hom_isHomLift {P Q : Total D n} (f : P ⟶ Q) :
    (forget D n).IsHomLift f.base f := sorry

/-- A total Postnikov-system morphism lifts any propositionally equal base arrow. -/
@[stacks 0D7Z "hom-lift transport for the total Postnikov-system projection"]
theorem isHomLift_of_eq {P Q : Total D n} {g : P.base ⟶ Q.base} (f : P ⟶ Q)
    (h : g = f.base) :
    (forget D n).IsHomLift g f := sorry

/-- The hom-lift predicate for the Postnikov-system projection is exactly equality with the stored
base component. -/
@[simp, stacks 0D7Z "hom-lift characterization for the total Postnikov-system projection"]
theorem isHomLift_iff {P Q : Total D n} (g : P.base ⟶ Q.base) (f : P ⟶ Q) :
    (forget D n).IsHomLift g f ↔ g = f.base := sorry

end CategoryTheory.PostnikovSystem.Total
