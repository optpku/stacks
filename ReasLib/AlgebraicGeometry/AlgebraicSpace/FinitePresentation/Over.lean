module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Algebraic spaces of finite presentation over a scheme

The full subcategory `FP_T` of algebraic spaces over a scheme `T` whose
structure morphism to `T` is of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The object property of being of finite presentation over the base scheme. -/
abbrev finitePresentationOverProperty (T : Scheme.{u}) :
    ObjectProperty (AlgebraicSpace T) :=
  fun X ↦ FinitePresentation (SchemeRealization.toBase X)

/-- The full subcategory of algebraic spaces of finite presentation over a scheme
`T`. -/
abbrev FinitePresentationOver (T : Scheme.{u}) :=
  (finitePresentationOverProperty T).FullSubcategory

namespace FinitePresentationOver

/-- The inclusion of algebraic spaces of finite presentation over `T` into all
algebraic spaces over `T`. -/
abbrev inclusion (T : Scheme.{u}) :
    FinitePresentationOver T ⥤ AlgebraicSpace T :=
  (finitePresentationOverProperty T).ι

/-- Package an algebraic space of finite presentation over `T` as an object of
`FinitePresentationOver T`. -/
def of {T : Scheme.{u}} (X : AlgebraicSpace T) (h : FinitePresentation (SchemeRealization.toBase X)) :
    FinitePresentationOver T :=
  ⟨X, h⟩

/-- The underlying algebraic space of `FinitePresentationOver.of X h` is `X`. -/
@[simp]
theorem of_obj {T : Scheme.{u}} (X : AlgebraicSpace T)
    (h : FinitePresentation (SchemeRealization.toBase X)) :
    (of X h).obj = X :=
  rfl

/-- An object of `FinitePresentationOver T` is of finite presentation over `T`. -/
instance condition {T : Scheme.{u}} (X : FinitePresentationOver T) :
    FinitePresentation (SchemeRealization.toBase X.obj) :=
  X.property

/-- Membership in `FinitePresentationOver T` is finite presentation of `toBase`. -/
theorem mem_iff {T : Scheme.{u}} (X : AlgebraicSpace T) :
    FinitePresentation (SchemeRealization.toBase X) ↔ ∃ Y : FinitePresentationOver T, Y.obj = X :=
  sorry

end FinitePresentationOver

end AlgebraicGeometry.AlgebraicSpace
