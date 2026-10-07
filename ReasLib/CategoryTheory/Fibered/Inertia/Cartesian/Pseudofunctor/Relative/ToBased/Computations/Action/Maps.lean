module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.ToBased.Construction
public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.MapArrow.Computations

/-!
# Square-map computations for the fibred-to-based pseudo-comma facade

This leaf includes the selected square comparison isomorphism and both of its directional
component formulas.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

/-- Forgetting an invertibly commuting fibred square applies `toBased` to its left endpoint map. -/
@[simp]
theorem toBased.map.left
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : S ⟶ T) :
    Bicategory.PseudoComma.left ((toBased C).map f) =
      (FiberedCategoryOver.toBased C).map (Bicategory.PseudoComma.left f) := sorry

/-- Forgetting an invertibly commuting fibred square applies `toBased` to its right endpoint map. -/
@[simp]
theorem toBased.map.right
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : S ⟶ T) :
    Bicategory.PseudoComma.right ((toBased C).map f) =
      (FiberedCategoryOver.toBased C).map (Bicategory.PseudoComma.right f) := sorry

/-- The comparison cell of a forgotten fibred square is the mapped source cell surrounded by
the composition comparisons of the forgetful pseudofunctor. -/
@[simp]
theorem toBased.map.cell
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : S ⟶ T) :
    Bicategory.PseudoComma.cell ((toBased C).map f) =
      ((FiberedCategoryOver.toBased C).toPseudofunctor.mapComp
          (Bicategory.PseudoComma.left f) T.hom).inv ≫
        (FiberedCategoryOver.toBased C).toPseudofunctor.map₂
          (Bicategory.PseudoComma.cell f) ≫
          ((FiberedCategoryOver.toBased C).toPseudofunctor.mapComp
            S.hom (Bicategory.PseudoComma.right f)).hom := sorry

/-- The selected comparison isomorphism of a forgotten fibred square is the mapped source
comparison surrounded by the composition comparisons of the forgetful pseudofunctor. -/
@[simp]
theorem toBased.map.cellIso
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : S ⟶ T) :
    Bicategory.PseudoComma.cellIso ((toBased C).map f) =
      (((FiberedCategoryOver.toBased C).toPseudofunctor.mapComp
        (Bicategory.PseudoComma.left f) T.hom).symm ≪≫
        (FiberedCategoryOver.toBased C).toPseudofunctor.map₂Iso
          (Bicategory.PseudoComma.cellIso f)) ≪≫
        (FiberedCategoryOver.toBased C).toPseudofunctor.mapComp
          S.hom (Bicategory.PseudoComma.right f) := sorry

/-- The forward comparison cell of a forgotten fibred square is the explicit mapped paste. -/
@[simp]
theorem toBased.map.cellIso.hom
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : S ⟶ T) :
    (Bicategory.PseudoComma.cellIso ((toBased C).map f)).hom =
      ((FiberedCategoryOver.toBased C).toPseudofunctor.mapComp
          (Bicategory.PseudoComma.left f) T.hom).inv ≫
        (FiberedCategoryOver.toBased C).toPseudofunctor.map₂
          (Bicategory.PseudoComma.cell f) ≫
          ((FiberedCategoryOver.toBased C).toPseudofunctor.mapComp
            S.hom (Bicategory.PseudoComma.right f)).hom := sorry

/-- The inverse comparison cell of a forgotten fibred square is the reverse mapped paste. -/
@[simp]
theorem toBased.map.cellIso.inv
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : S ⟶ T) :
    (Bicategory.PseudoComma.cellIso ((toBased C).map f)).inv =
      ((FiberedCategoryOver.toBased C).toPseudofunctor.mapComp
          S.hom (Bicategory.PseudoComma.right f)).inv ≫
        (FiberedCategoryOver.toBased C).toPseudofunctor.map₂
          (Bicategory.PseudoComma.cellIso f).inv ≫
          ((FiberedCategoryOver.toBased C).toPseudofunctor.mapComp
            (Bicategory.PseudoComma.left f) T.hom).hom := sorry

end FiberedCategoryOver.RelativeInertia.pseudoComma

end CategoryTheory
