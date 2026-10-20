/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeSquare.Independence
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.Proper
import StacksCheckRecall

/-!
# Independence of the outer 2-cell for dotted arrows

Proper target inertia makes the dotted-arrow category independent of the outer
comparison and makes existence equivalent to two triangles without coherence.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids.Inertia (forget)

universe u

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}

/- Lemma 101.39.3: proper target inertia makes the category of dotted arrows
independent, up to noncanonical equivalence, of the chosen outer comparison. -/
@[stacks 0CLD]
#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.dottedArrow_equivalence_of_iso :
  Groupoids.Hom.has (@AlgebraicSpace.Proper S) (forget.{u + 1, u, u, u + 1} Y) →
    ∀ (sq : ValuativeCommSq f) (iso' : sq.verticalMap ≫ sq.i₂ ≅ sq.i₁ ≫ f),
    Nonempty (DottedArrow sq.toCone ≌ DottedArrow (sq.replaceIso iso').toCone))

/- Lemma 101.39.3: existence of a dotted arrow is equivalent to a fill-in with
two 2-commutative triangles, without requiring their outer coherence. -/
@[stacks 0CLD]
#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.nonempty_dottedArrow_iff_triangles :
  Groupoids.Hom.has (@AlgebraicSpace.Proper S) (forget.{u + 1, u, u, u + 1} Y) →
    ∀ (sq : ValuativeCommSq f),
    (Nonempty (DottedArrow sq.toCone) ↔ Nonempty (DottedArrow.Triangles sq.toCone)))

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.nonempty_dottedArrow_iff_forall_iso :
  Groupoids.Hom.has (@AlgebraicSpace.Proper S) (forget.{u + 1, u, u, u + 1} Y) →
    ∀ (sq : ValuativeCommSq f),
    (Nonempty (DottedArrow sq.toCone) ↔
      ∀ iso' : sq.verticalMap ≫ sq.i₂ ≅ sq.i₁ ≫ f,
        Nonempty (DottedArrow (sq.replaceIso iso').toCone)))

section SeparatedOver

variable [IsSeparatedOver Y]

#check (AlgebraicGeometry.AlgebraicStack.forget_has_proper_of_isSeparatedOver :
  Groupoids.Hom.has (@AlgebraicSpace.Proper S)
    (forget.{u + 1, u, u, u + 1} Y))

end SeparatedOver

section Separated

variable [IsSeparated Y]

#check (AlgebraicGeometry.AlgebraicStack.forget_has_proper_of_isSeparated :
  Groupoids.Hom.has (@AlgebraicSpace.Proper S)
    (forget.{u + 1, u, u, u + 1} Y))

end Separated
