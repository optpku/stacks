module

public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
public import ReasLib.CategoryTheory.InverseSystem.Sequential
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential internal-Hom and dual-tensor towers

This leaf owns the inverse system obtained by applying internal Hom contravariantly to a
sequential diagram, the source-facing tensor-dual inverse system, and their canonical comparison.
For dualizable stages the comparison is invertible.  The separate homotopy-colimit leaf uses
this API without making basic tower consumers import pretriangulated infrastructure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

noncomputable section

universe u v

namespace CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [MonoidalClosed C]

namespace InternalHom

/-- The inverse system obtained by applying internal Hom into `E` contravariantly to a
sequential diagram `K`. -/
@[stacks 0DJI "sequential internal-Hom inverse system"]
abbrev tower (K : ℕ ⥤ C) (E : C) : SequentialInverseSystem C :=
  K.op ⋙ (internalHom (C := C)).flip.obj E

/-- The `n`th object of the internal-Hom inverse system is `(ihom (K.obj n)).obj E`. -/
@[simp]
theorem tower_obj (K : ℕ ⥤ C) (E : C) (n : ℕ) :
    (tower K E).obj (op n) = (ihom (K.obj n)).obj E := sorry

/-- A transition in the internal-Hom inverse system is precomposition by the corresponding
map of the sequential diagram. -/
@[simp]
theorem tower_transitionMap (K : ℕ ⥤ C) (E : C) {i j : ℕ} (hij : i ≤ j) :
    (tower K E).transitionMap hij =
      (pre (K.map (homOfLE hij))).app E := sorry

end InternalHom

namespace Dual

/-- The inverse system `n ↦ E ⊗ dual (K.obj n)` attached to a sequential diagram. -/
@[stacks 0DJI "sequential dual-tensor inverse system",
  stacks 0A0A "dual-tensor inverse system"]
abbrev tensorTower (K : ℕ ⥤ C) (E : C) : SequentialInverseSystem C :=
  InternalHom.tower K (𝟙_ C) ⋙ tensorLeft E

/-- The `n`th object of the dual-tensor inverse system is `E ⊗ dual (K.obj n)`. -/
@[simp]
theorem tensorTower_obj (K : ℕ ⥤ C) (E : C) (n : ℕ) :
    (tensorTower K E).obj (op n) = E ⊗ dual (K.obj n) := sorry

/-- A transition in the dual-tensor inverse system is obtained by tensoring the
contravariant dual map with `E`. -/
@[simp]
theorem tensorTower_transitionMap
    (K : ℕ ⥤ C) (E : C) {i j : ℕ} (hij : i ≤ j) :
    (tensorTower K E).transitionMap hij =
      E ◁ (pre (K.map (homOfLE hij))).app (𝟙_ C) := sorry

variable [BraidedCategory C]

/-- The canonical morphism from the dual-tensor inverse system to the internal-Hom inverse
system. -/
@[stacks 0DJI "dual-tensor to internal-Hom tower comparison"]
def tensorComparisonHom (K : ℕ ⥤ C) (E : C) :
    tensorTower K E ⟶ InternalHom.tower K E :=
  Functor.whiskerLeft K.op (tensorComparisonNatTrans E)

/-- The component of the tower comparison is the closed-monoidal tensor comparison. -/
@[simp]
theorem tensorComparisonHom_app (K : ℕ ⥤ C) (E : C) (n : ℕᵒᵖ) :
    (tensorComparisonHom K E).app n = tensorComparison (K.obj n.unop) E := sorry

/-- The dual-tensor tower comparison is invertible when every stage of the sequential diagram
is right-dualizable. -/
@[stacks 0DJI "dualizable-stage tower comparison"]
theorem isIso_tensorComparisonHom
    (K : ℕ ⥤ C) (E : C) (hK : ∀ n, IsRightDualizable (K.obj n)) :
    IsIso (tensorComparisonHom K E) := sorry

end Dual

end CategoryTheory.MonoidalClosed

end
