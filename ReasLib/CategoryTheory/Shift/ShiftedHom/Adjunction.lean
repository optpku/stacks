module

public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.CategoryTheory.Shift.Adjunction
public import ReasLib.CategoryTheory.Adjunction.Linear
import Mathlib.Tactic.CrossRefAttribute

/-!
# Shifted Hom along an adjunction

The right-adjoint shift comparison moves a shift through `G` and then applies the linear
adjunction equivalence.  This is the generic owner for the shifted representability step used by
derived tensor-Hom constructions; no derived category or chosen model appears here.

The pointwise equivalence works across independent category and Hom universes.  A plain
categorical equivalence is exposed first; the linear companion adds only the hypotheses needed by
the module-valued API.
-/

@[expose] public section

noncomputable section

universe uR uM vC uC vD uD

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {M : Type uM} [AddMonoid M]
variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [HasShift C M] [HasShift D M]
variable {F : C ⥤ D} {G : D ⥤ C}

/-- A right-adjoint shift comparison: move the target shift through `G`, then uncurry along
`adj`.  The shift index is any additive monoid `M`, and the category and Hom universes of `C` and
`D` are independent. -/
@[stacks 09LN "shifted-Hom equivalence along an adjunction"]
noncomputable def shiftedHomEquiv (adj : F ⊣ G) [G.CommShift M]
    (X : C) (Y : D) (n : M) :
    ShiftedHom X (G.obj Y) n ≃ ShiftedHom (F.obj X) Y n :=
  (Iso.homCongr (Iso.refl X) ((G.commShiftIso n).symm.app Y)).trans
    (adj.homEquiv X (Y⟦n⟧)).symm

/-- The forward shifted-adjunction equivalence moves the shift through the right adjoint before
uncurrying. -/
@[simp, stacks 09LN "forward plain shifted-Hom adjunction comparison"]
theorem shiftedHomEquiv_apply (adj : F ⊣ G) [G.CommShift M]
    (X : C) (Y : D) (n : M) (f : ShiftedHom X (G.obj Y) n) :
    adj.shiftedHomEquiv X Y n f =
      (adj.homEquiv X (Y⟦n⟧)).symm
        (f ≫ (G.commShiftIso n).inv.app Y) := sorry

/-- The inverse shifted-adjunction equivalence curries and then moves the shift back through the
right adjoint. -/
@[simp, stacks 09LN "inverse plain shifted-Hom adjunction comparison"]
theorem shiftedHomEquiv_symm_apply (adj : F ⊣ G) [G.CommShift M]
    (X : C) (Y : D) (n : M) (g : ShiftedHom (F.obj X) Y n) :
    (adj.shiftedHomEquiv X Y n).symm g =
      adj.homEquiv X (Y⟦n⟧) g ≫ (G.commShiftIso n).hom.app Y := sorry

/-! The pointwise comparison is natural in both variables. -/

/-- Source naturality of the forward shifted-Hom adjunction comparison. -/
@[reassoc, stacks 09LN "source naturality of the plain shifted-Hom adjunction comparison"]
theorem shiftedHomEquiv_naturality_left (adj : F ⊣ G) [G.CommShift M]
    {X X' : C} (f : X' ⟶ X) (Y : D) (n : M)
    (g : ShiftedHom X (G.obj Y) n) :
    adj.shiftedHomEquiv X' Y n (f ≫ g) =
      F.map f ≫ adj.shiftedHomEquiv X Y n g := sorry

/-- Target naturality of the forward shifted-Hom adjunction comparison. -/
@[reassoc, stacks 09LN "target naturality of the plain shifted-Hom adjunction comparison"]
theorem shiftedHomEquiv_naturality_right (adj : F ⊣ G) [G.CommShift M]
    (X : C) {Y Y' : D} (h : Y ⟶ Y') (n : M)
    (g : ShiftedHom X (G.obj Y) n) :
    adj.shiftedHomEquiv X Y' n (g ≫ (G.map h)⟦n⟧') =
      adj.shiftedHomEquiv X Y n g ≫ h⟦n⟧' := sorry

/-- Source naturality of the inverse plain shifted-Hom adjunction comparison. -/
@[reassoc, stacks 09LN "source naturality of the inverse plain shifted-Hom adjunction comparison"]
theorem shiftedHomEquiv_symm_naturality_left (adj : F ⊣ G) [G.CommShift M]
    {X X' : C} (f : X' ⟶ X) (Y : D) (n : M)
    (g : ShiftedHom (F.obj X) Y n) :
    (adj.shiftedHomEquiv X' Y n).symm (F.map f ≫ g) =
      f ≫ (adj.shiftedHomEquiv X Y n).symm g := sorry

/-- Target naturality of the inverse plain shifted-Hom adjunction comparison. -/
@[reassoc, stacks 09LN "target naturality of the inverse plain shifted-Hom adjunction comparison"]
theorem shiftedHomEquiv_symm_naturality_right (adj : F ⊣ G) [G.CommShift M]
    (X : C) {Y Y' : D} (h : Y ⟶ Y') (n : M)
    (g : ShiftedHom (F.obj X) Y n) :
    (adj.shiftedHomEquiv X Y' n).symm (g ≫ h⟦n⟧') =
      (adj.shiftedHomEquiv X Y n).symm g ≫
        (G.map h)⟦n⟧' := sorry

section Linear

variable {R : Type uR} [Semiring R]
variable [Preadditive C] [Preadditive D]
variable [Linear R C] [Linear R D]

/-- The linear form of `shiftedHomEquiv`, for linear categories and a linear left adjoint. -/
@[stacks 09LN "linear shifted-Hom equivalence along an adjunction"]
noncomputable def shiftedHomLinearEquiv (adj : F ⊣ G) [G.CommShift M]
    [F.Additive] [F.Linear R] (X : C) (Y : D) (n : M) :
    ShiftedHom X (G.obj Y) n ≃ₗ[R] ShiftedHom (F.obj X) Y n :=
  (Linear.homCongr R (Iso.refl X) ((G.commShiftIso n).symm.app Y)).trans
    (adj.homLinearEquiv (k := R) X (Y⟦n⟧)).symm

/-- The forward shifted-adjunction comparison is the explicit composition through the right
adjoint's shift isomorphism and the adjunction Hom equivalence. -/
@[simp, stacks 09LN "forward shifted-Hom adjunction comparison"]
theorem shiftedHomLinearEquiv_apply (adj : F ⊣ G) [G.CommShift M]
    [F.Additive] [F.Linear R] (X : C) (Y : D) (n : M)
    (f : ShiftedHom X (G.obj Y) n) :
    adj.shiftedHomLinearEquiv (R := R) X Y n f =
      (adj.homLinearEquiv (k := R) X (Y⟦n⟧)).symm
        (f ≫ (G.commShiftIso n).inv.app Y) := sorry

/-- The inverse shifted-adjunction comparison is currying followed by the right adjoint's shift
isomorphism. -/
@[simp, stacks 09LN "inverse shifted-Hom adjunction comparison"]
theorem shiftedHomLinearEquiv_symm_apply (adj : F ⊣ G) [G.CommShift M]
    [F.Additive] [F.Linear R] (X : C) (Y : D) (n : M)
    (g : ShiftedHom (F.obj X) Y n) :
    (adj.shiftedHomLinearEquiv (R := R) X Y n).symm g =
      adj.homLinearEquiv (k := R) X (Y⟦n⟧) g ≫ (G.commShiftIso n).hom.app Y := sorry

/-- Source naturality of the forward linear shifted-Hom adjunction comparison. -/
@[reassoc, stacks 09LN "source naturality of the linear shifted-Hom adjunction comparison"]
theorem shiftedHomLinearEquiv_naturality_left (adj : F ⊣ G) [G.CommShift M]
    [F.Additive] [F.Linear R] {X X' : C} (f : X' ⟶ X) (Y : D) (n : M)
    (g : ShiftedHom X (G.obj Y) n) :
    adj.shiftedHomLinearEquiv (R := R) X' Y n (f ≫ g) =
      F.map f ≫ adj.shiftedHomLinearEquiv (R := R) X Y n g := sorry

/-- Target naturality of the forward linear shifted-Hom adjunction comparison. -/
@[reassoc, stacks 09LN "target naturality of the linear shifted-Hom adjunction comparison"]
theorem shiftedHomLinearEquiv_naturality_right (adj : F ⊣ G) [G.CommShift M]
    [F.Additive] [F.Linear R] (X : C) {Y Y' : D} (h : Y ⟶ Y') (n : M)
    (g : ShiftedHom X (G.obj Y) n) :
    adj.shiftedHomLinearEquiv (R := R) X Y' n (g ≫ (G.map h)⟦n⟧') =
      adj.shiftedHomLinearEquiv (R := R) X Y n g ≫ h⟦n⟧' := sorry

/-- Source naturality of the inverse linear shifted-Hom adjunction comparison. -/
@[reassoc, stacks 09LN "source naturality of the inverse linear shifted-Hom adjunction comparison"]
theorem shiftedHomLinearEquiv_symm_naturality_left (adj : F ⊣ G) [G.CommShift M]
    [F.Additive] [F.Linear R] {X X' : C} (f : X' ⟶ X) (Y : D) (n : M)
    (g : ShiftedHom (F.obj X) Y n) :
    (adj.shiftedHomLinearEquiv (R := R) X' Y n).symm (F.map f ≫ g) =
      f ≫ (adj.shiftedHomLinearEquiv (R := R) X Y n).symm g := sorry

/-- Target naturality of the inverse linear shifted-Hom adjunction comparison. -/
@[reassoc, stacks 09LN "target naturality of the inverse linear shifted-Hom adjunction comparison"]
theorem shiftedHomLinearEquiv_symm_naturality_right (adj : F ⊣ G) [G.CommShift M]
    [F.Additive] [F.Linear R] (X : C) {Y Y' : D} (h : Y ⟶ Y') (n : M)
    (g : ShiftedHom (F.obj X) Y n) :
    (adj.shiftedHomLinearEquiv (R := R) X Y' n).symm (g ≫ h⟦n⟧') =
      (adj.shiftedHomLinearEquiv (R := R) X Y n).symm g ≫
        (G.map h)⟦n⟧' := sorry

end Linear

end CategoryTheory.Adjunction
