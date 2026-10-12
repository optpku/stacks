/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Duality
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.BraidedClosed
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Dualizable

/-!
# Dualizable objects in braided closed monoidal categories

@stack 08DQ
@stack 0FPC

This leaf combines explicit exact pairings with the canonical closed-monoidal dual.  It owns
the functorial tensor/internal-Hom isomorphism, invertibility of the canonical tensor and
bidual comparisons, and the induced equivalence on morphisms from the tensor unit.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [BraidedCategory C] [MonoidalClosed C]

namespace ExactPairing

/-- A chosen right dual represents the canonical internal Hom out of the paired object. -/
@[stacks 08DQ "tensor-dual/internal-Hom natural isomorphism"]
def tensorIsoIhom {X Y : C} (p : ExactPairing X Y) :
    tensorRight Y ≅ ihom X :=
  p.rightInternalHomIso (RightInternalHom.ofBraidedClosed (C := C))

end ExactPairing

namespace MonoidalClosed.Dual

/-- In a braided closed monoidal category, an object is right-dualizable exactly when its
canonical tensor-to-endomorphism comparison is an isomorphism. -/
@[stacks 0FPC "closed-dual criterion", stacks 0FPD "closed-dual criterion"]
theorem isRightDualizable_iff (X : C) :
    IsRightDualizable X ↔ IsIso (tensorIhomUnitToEnd X) := sorry

/-- Tensoring with the canonical closed-monoidal dual represents the internal Hom out of a
dualizable object. -/
@[stacks 08DQ "canonical tensor-dual/internal-Hom natural isomorphism"]
def tensorIsoIhom (X : C) [IsIso (tensorIhomUnitToEnd X)] :
    tensorRight (dual X) ≅ ihom X :=
  (exactPairing X).tensorIsoIhom

/-- The forward component of `tensorIsoIhom` is the canonical tensor/internal-Hom comparison. -/
@[simp]
theorem tensorIsoIhom_hom_app
    (X M : C) [IsIso (tensorIhomUnitToEnd X)] :
    (tensorIsoIhom X).hom.app M = tensorComparison X M := sorry

/-- For a dualizable object, every component of the canonical tensor/internal-Hom comparison
is an isomorphism. -/
@[stacks 08DQ "canonical tensor-dual/internal-Hom comparison", instance]
theorem isIso_tensorComparison
    (X M : C) [IsIso (tensorIhomUnitToEnd X)] :
    IsIso (tensorComparison X M) := sorry

/-- The canonical isomorphism from a dualizable object to its closed-monoidal bidual. -/
@[stacks 08DQ "canonical bidual isomorphism"]
def bidualIso
    (X : C) [IsIso (tensorIhomUnitToEnd X)] :
    X ≅ dual (dual X) :=
  leftDualIso (exactPairing X)

/-- The forward map of `bidualIso` is the canonical bidual comparison. -/
@[simp]
theorem bidualIso_hom
    (X : C) [IsIso (tensorIhomUnitToEnd X)] :
    (bidualIso X).hom = bidualComparison X := sorry

/-- The canonical bidual comparison of a dualizable object is an isomorphism. -/
@[stacks 08DQ "canonical bidual comparison", instance]
theorem isIso_bidualComparison
    (X : C) [IsIso (tensorIhomUnitToEnd X)] :
    IsIso (bidualComparison X) := sorry

/-- Morphisms from the tensor unit into `M ⊗ dual X` are canonically equivalent to
morphisms from `X` into `M`. -/
@[stacks 08DQ "Hom equivalence"]
def homEquiv (X M : C) [IsIso (tensorIhomUnitToEnd X)] :
    (𝟙_ C ⟶ M ⊗ dual X) ≃ (X ⟶ M) :=
  ((Iso.refl (𝟙_ C)).homCongr ((tensorIsoIhom X).app M)).trans
    MonoidalClosed.curryHomEquiv'.symm

/-- The canonical duality Hom-equivalence is the map obtained from
`tensorComparison` by closed-monoidal uncurrying. -/
@[simp]
theorem homEquiv_apply
    (X M : C) [IsIso (tensorIhomUnitToEnd X)]
    (s : 𝟙_ C ⟶ M ⊗ dual X) :
    homEquiv X M s = homComparison X M s := sorry

/-- The inverse canonical duality Hom-equivalence is coevaluation followed by tensoring the
given morphism with the identity of the dual. -/
@[simp]
theorem homEquiv_symm_apply
    (X M : C) [IsIso (tensorIhomUnitToEnd X)] (f : X ⟶ M) :
    (homEquiv X M).symm f = coevaluation X ≫ f ▷ dual X := sorry

/-- The function underlying the canonical Hom comparison is bijective for a dualizable object. -/
theorem homComparison_bijective
    (X M : C) [IsIso (tensorIhomUnitToEnd X)] :
    Function.Bijective (homComparison X M) := sorry

end MonoidalClosed.Dual

namespace IsRightDualizable

/-- Right dualizability makes the canonical tensor-to-endomorphism comparison invertible. -/
theorem isIso_tensorIhomUnitToEnd
    {X : C} (hX : IsRightDualizable X) :
    IsIso (MonoidalClosed.tensorIhomUnitToEnd X) := sorry

/-- The closed-monoidal dual of a right-dualizable object is right-dualizable. -/
@[stacks 08DQ "dual perfectness, categorical form"]
theorem dual
    {X : C} (hX : IsRightDualizable X) :
    IsRightDualizable (MonoidalClosed.dual X) := sorry

/-- Tensoring with the closed-monoidal dual of a right-dualizable object represents its
internal Hom. -/
@[stacks 08DQ "tensor/internal-Hom comparison"]
theorem isIso_tensorComparison
    {X : C} (hX : IsRightDualizable X) (M : C) :
    IsIso (MonoidalClosed.Dual.tensorComparison X M) := sorry

/-- The canonical bidual comparison of a right-dualizable object is an isomorphism. -/
@[stacks 08DQ "bidual comparison"]
theorem isIso_bidualComparison
    {X : C} (hX : IsRightDualizable X) :
    IsIso (MonoidalClosed.Dual.bidualComparison X) := sorry

/-- The canonical comparison on morphisms from the tensor unit is bijective for a
right-dualizable object. -/
@[stacks 08DQ "Hom comparison"]
theorem homComparison_bijective
    {X : C} (hX : IsRightDualizable X) (M : C) :
    Function.Bijective (MonoidalClosed.Dual.homComparison X M) := sorry

end IsRightDualizable

end CategoryTheory
