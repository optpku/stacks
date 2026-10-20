/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving.TwoFibreProduct
import StacksCheckRecall

/-!
# Fibre products of limit-preserving categories fibred in groupoids

Limit preservation on objects and full limit preservation are stable under
2-fibre products of categories fibred in groupoids
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

/- Lemma 98.11.2 (1): if `X ⟶ (Sch/S)_fppf` and `Z ⟶ (Sch/S)_fppf` are limit
preserving on objects and `Y` is limit preserving, then
`X ×_Y Z ⟶ (Sch/S)_fppf` is limit preserving on objects. -/
@[stacks 07XM] #check
  (AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects.twoFibreProduct :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      (p : X ⟶ Y) (q : Z ⟶ Y)
      [AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
        (baseProjection.{u + 1, u, u + 1} X)]
      [AlgebraicGeometry.Groupoids.LimitPreserving Y]
      [AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
        (baseProjection.{u + 1, u, u + 1} Z)],
    AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
      (baseProjection.{u + 1, u, u + 1}
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q)))

/- Lemma 98.11.2 (2): if `X`, `Y`, and `Z` are limit preserving, then so is
the 2-fibre product `X ×_Y Z`. -/
@[stacks 07XM] #check (AlgebraicGeometry.Groupoids.LimitPreserving.twoFibreProduct :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Z ⟶ Y)
    [AlgebraicGeometry.Groupoids.LimitPreserving X]
    [AlgebraicGeometry.Groupoids.LimitPreserving Y]
    [AlgebraicGeometry.Groupoids.LimitPreserving Z],
  AlgebraicGeometry.Groupoids.LimitPreserving
    (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q))
