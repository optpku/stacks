module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibre products of limit-preserving categories fibred in groupoids

Limit preservation on objects, and the stronger object-level limit-preserving
property, are stable under 2-fibre products of categories fibred in groupoids
over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace LimitPreservingOnObjects

/-- Lemma 98.11.2 (1): if `X ⟶ (Sch/S)_fppf` and `Z ⟶ (Sch/S)_fppf` are limit
preserving on objects and `Y` is limit preserving, then
`X ×_Y Z ⟶ (Sch/S)_fppf` is limit preserving on objects. -/
@[stacks 07XM]
theorem twoFibreProduct {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Z ⟶ Y)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} X)]
    [LimitPreserving Y]
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} Z)] :
    LimitPreservingOnObjects
      (baseProjection.{u + 1, u, u + 1}
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q)) :=
  sorry

end LimitPreservingOnObjects

end AlgebraicGeometry.Groupoids.Hom

namespace AlgebraicGeometry.Groupoids.LimitPreserving

/-- Lemma 98.11.2 (2): if `X`, `Y`, and `Z` are limit preserving, then so is
the 2-fibre product `X ×_Y Z`. -/
@[stacks 07XM]
theorem twoFibreProduct {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Z ⟶ Y)
    [LimitPreserving X] [LimitPreserving Y] [LimitPreserving Z] :
    LimitPreserving (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q) :=
  sorry

end AlgebraicGeometry.Groupoids.LimitPreserving
