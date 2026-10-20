module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeSquare
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Triangles
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps.Construction

/-!
# Independence of the outer 2-cell for dotted arrows

If the inertia morphism of the target algebraic stack is proper, the category
of dotted arrows of a valuative 2-square is independent of the choice of outer
2-cell up to noncanonical equivalence. Existence of a dotted arrow is then
equivalent to existence of two 2-commutative triangles, without requiring
those 2-cells to compose to the outer 2-cell.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia (forget)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace ValuativeCommSq

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}

/-- Rebuild a valuative commutative square with the same valuation ring, solid
arrows, and structure morphism, replacing only the outer 2-cell. -/
def replaceIso (sq : ValuativeCommSq f)
    (iso' : sq.verticalMap ≫ sq.i₂ ≅ sq.i₁ ≫ f) : ValuativeCommSq f :=
  of sq.R sq.K sq.structureHom sq.i₁ sq.i₂ iso'

/-- The valuation ring of `replaceIso` is the original valuation ring. -/
@[simp]
theorem replaceIso_R (sq : ValuativeCommSq f)
    (iso' : sq.verticalMap ≫ sq.i₂ ≅ sq.i₁ ≫ f) : (sq.replaceIso iso').R = sq.R :=
  sorry

/-- The top map of `replaceIso` is the original top map. -/
@[simp]
theorem replaceIso_i₁ (sq : ValuativeCommSq f)
    (iso' : sq.verticalMap ≫ sq.i₂ ≅ sq.i₁ ≫ f) : (sq.replaceIso iso').i₁ = sq.i₁ :=
  sorry

/-- The bottom map of `replaceIso` is the original bottom map. -/
@[simp]
theorem replaceIso_i₂ (sq : ValuativeCommSq f)
    (iso' : sq.verticalMap ≫ sq.i₂ ≅ sq.i₁ ≫ f) : (sq.replaceIso iso').i₂ = sq.i₂ :=
  sorry

/-- The outer 2-cell of `replaceIso` is the newly supplied 2-isomorphism. -/
@[simp]
theorem replaceIso_iso (sq : ValuativeCommSq f)
    (iso' : sq.verticalMap ≫ sq.i₂ ≅ sq.i₁ ≫ f) :
    (sq.replaceIso iso').iso = iso' :=
  sorry

/-- If the inertia morphism `I_Y ⟶ Y` is proper, then the
category of dotted arrows of a valuative 2-square is independent, up to
noncanonical equivalence, of the choice of the outer 2-cell. -/
@[stacks 0CLD]
theorem dottedArrow_equivalence_of_iso
    (h_inertia :
      Groupoids.Hom.has (@AlgebraicSpace.Proper S) (forget.{u + 1, u, u, u + 1} Y))
    (sq : ValuativeCommSq f) (iso' : sq.verticalMap ≫ sq.i₂ ≅ sq.i₁ ≫ f) :
    Nonempty (DottedArrow sq.toCone ≌ DottedArrow (sq.replaceIso iso').toCone) :=
  sorry

/-- If the inertia morphism `I_Y ⟶ Y` is proper, then
existence of a dotted arrow is equivalent to existence of a fill-in with two
2-commutative triangles, without requiring those 2-cells to compose to the
outer 2-cell. -/
@[stacks 0CLD]
theorem nonempty_dottedArrow_iff_triangles
    (h_inertia :
      Groupoids.Hom.has (@AlgebraicSpace.Proper S) (forget.{u + 1, u, u, u + 1} Y))
    (sq : ValuativeCommSq f) :
    Nonempty (DottedArrow sq.toCone) ↔ Nonempty (DottedArrow.Triangles sq.toCone) :=
  sorry

/-- If the inertia morphism `I_Y ⟶ Y` is proper, then a valuative 2-square
admits a dotted arrow for one outer 2-cell if and only if it admits a dotted
arrow for every outer 2-cell. -/
theorem nonempty_dottedArrow_iff_forall_iso
    (h_inertia :
      Groupoids.Hom.has (@AlgebraicSpace.Proper S) (forget.{u + 1, u, u, u + 1} Y))
    (sq : ValuativeCommSq f) :
    Nonempty (DottedArrow sq.toCone) ↔
      ∀ iso' : sq.verticalMap ≫ sq.i₂ ≅ sq.i₁ ≫ f,
        Nonempty (DottedArrow (sq.replaceIso iso').toCone) :=
  sorry

end ValuativeCommSq

end AlgebraicGeometry.AlgebraicStack
