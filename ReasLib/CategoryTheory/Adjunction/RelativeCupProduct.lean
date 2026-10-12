/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor maps on right adjoints

For monoidal categories, the canonical tensor map on a right adjoint is already
`Functor.LaxMonoidal.μ`, supplied by `Adjunction.rightAdjointLaxMonoidal`.  This file adds the raw
`_of` bridge needed before the tensor operations and their comparison have been bundled into
monoidal structures.  The bridge assumes only a morphism family, not invertibility or coherence.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe vC vD uC uD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {L : C ⥤ D} {R : D ⥤ C}

/-- A right adjoint together with a chosen tensor-compatible left adjoint.  This is the raw model
used when the ambient tensor operations have not yet been bundled as monoidal structures. -/
@[stacks 0B68 "tensor-compatible adjunction model"]
structure TensorModel (R : D ⥤ C) (tensorC : C ⥤ C ⥤ C)
    (tensorD : D ⥤ D ⥤ D) where
  /-- The chosen left adjoint. -/
  left : C ⥤ D
  /-- The adjunction exhibiting `left` as a left adjoint of `R`. -/
  adjunction : left ⊣ R
  /-- The tensor comparison on the left adjoint. -/
  comparison (X Y : C) :
    left.obj ((tensorC.obj X).obj Y) ≅
      (tensorD.obj (left.obj X)).obj (left.obj Y)

/-- The adjoint-side composite defining a raw tensor map on a right adjoint. -/
@[stacks 0B68 "right-adjoint tensor map adjoint composite"]
noncomputable def rightAdjointTensorMapAdjointOf
    (adj : L ⊣ R) (tensorC : C ⥤ C ⥤ C) (tensorD : D ⥤ D ⥤ D)
    (comparison : ∀ X Y,
      L.obj ((tensorC.obj X).obj Y) ⟶ (tensorD.obj (L.obj X)).obj (L.obj Y))
    (X Y : D) :
    L.obj ((tensorC.obj (R.obj X)).obj (R.obj Y)) ⟶ (tensorD.obj X).obj Y :=
  comparison (R.obj X) (R.obj Y) ≫
    (tensorD.map (adj.counit.app X)).app (L.obj (R.obj Y)) ≫
    (tensorD.obj X).map (adj.counit.app Y)

/-- The raw tensor map on a right adjoint obtained by transposing a tensor comparison and the two
adjunction counits.  Arguments follow tensor order: `X` precedes `Y` in both source and target. -/
@[stacks 0B68 "right-adjoint tensor map from a comparison"]
noncomputable def rightAdjointTensorMapOf
    (adj : L ⊣ R) (tensorC : C ⥤ C ⥤ C) (tensorD : D ⥤ D ⥤ D)
    (comparison : ∀ X Y,
      L.obj ((tensorC.obj X).obj Y) ⟶ (tensorD.obj (L.obj X)).obj (L.obj Y))
    (X Y : D) :
    (tensorC.obj (R.obj X)).obj (R.obj Y) ⟶ R.obj ((tensorD.obj X).obj Y) :=
  adj.homEquiv _ _
    (rightAdjointTensorMapAdjointOf adj tensorC tensorD comparison X Y)

/-- Transposing `rightAdjointTensorMapOf` back across the adjunction recovers its defining
adjoint-side composite. -/
@[stacks 0B68 "right-adjoint tensor map specification"]
theorem rightAdjointTensorMapOf_spec
    (adj : L ⊣ R) (tensorC : C ⥤ C ⥤ C) (tensorD : D ⥤ D ⥤ D)
    (comparison : ∀ X Y,
      L.obj ((tensorC.obj X).obj Y) ⟶ (tensorD.obj (L.obj X)).obj (L.obj Y))
    (X Y : D) :
    (adj.homEquiv ((tensorC.obj (R.obj X)).obj (R.obj Y))
        ((tensorD.obj X).obj Y)).symm
      (rightAdjointTensorMapOf adj tensorC tensorD comparison X Y) =
    rightAdjointTensorMapAdjointOf adj tensorC tensorD comparison X Y := sorry

/-! The names below are the source-facing cup-product layer.  The underlying construction is still
the generic right-adjoint tensor map above, so applications can move between the mathematical
description and the implementation without introducing a second map owner. -/

/-- The adjoint-side morphism underlying a relative derived cup product. -/
@[stacks 0B68 "relative cup-product adjoint map"]
noncomputable abbrev relativeDerivedCupProductAdjointMap
    (adj : L ⊣ R) (tensorC : C ⥤ C ⥤ C) (tensorD : D ⥤ D ⥤ D)
    (comparison : ∀ X Y,
      L.obj ((tensorC.obj X).obj Y) ⟶ (tensorD.obj (L.obj X)).obj (L.obj Y))
    (X Y : D) :
    L.obj ((tensorC.obj (R.obj X)).obj (R.obj Y)) ⟶ (tensorD.obj X).obj Y :=
  rightAdjointTensorMapAdjointOf adj tensorC tensorD comparison X Y

/-- The relative derived cup product associated to an adjunction and a pullback-tensor comparison.
The comparison is an explicit input because coherence is additional structure, not a consequence
of an arbitrary objectwise family of maps. -/
@[stacks 0B68 "relative derived cup product"]
noncomputable abbrev relativeDerivedCupProduct
    (adj : L ⊣ R) (tensorC : C ⥤ C ⥤ C) (tensorD : D ⥤ D ⥤ D)
    (comparison : ∀ X Y,
      L.obj ((tensorC.obj X).obj Y) ⟶ (tensorD.obj (L.obj X)).obj (L.obj Y))
    (X Y : D) :
    (tensorC.obj (R.obj X)).obj (R.obj Y) ⟶ R.obj ((tensorD.obj X).obj Y) :=
  rightAdjointTensorMapOf adj tensorC tensorD comparison X Y

/-- Transposing the relative derived cup product recovers its pullback-side composite. -/
@[stacks 0B68 "relative derived cup-product specification"]
theorem relativeDerivedCupProduct_spec
    (adj : L ⊣ R) (tensorC : C ⥤ C ⥤ C) (tensorD : D ⥤ D ⥤ D)
    (comparison : ∀ X Y,
      L.obj ((tensorC.obj X).obj Y) ⟶ (tensorD.obj (L.obj X)).obj (L.obj Y))
    (X Y : D) :
    (adj.homEquiv ((tensorC.obj (R.obj X)).obj (R.obj Y)) ((tensorD.obj X).obj Y)).symm
        (adj.relativeDerivedCupProduct tensorC tensorD comparison X Y) =
      adj.relativeDerivedCupProductAdjointMap tensorC tensorD comparison X Y := sorry

namespace TensorModel

variable {tensorC : C ⥤ C ⥤ C} {tensorD : D ⥤ D ⥤ D}

/-- The adjoint-side morphism underlying the cup product of a tensor-compatible adjunction
model. -/
@[stacks 0B68 "modeled relative cup-product adjoint map"]
noncomputable abbrev cupProductAdjoint
    (M : TensorModel R tensorC tensorD) (X Y : D) :
    M.left.obj ((tensorC.obj (R.obj X)).obj (R.obj Y)) ⟶
      (tensorD.obj X).obj Y :=
  M.adjunction.relativeDerivedCupProductAdjointMap tensorC tensorD
    (fun A B => (M.comparison A B).hom) X Y

/-- The cup product selected by a tensor-compatible adjunction model. -/
@[stacks 0B68 "modeled relative cup product"]
noncomputable abbrev cupProduct
    (M : TensorModel R tensorC tensorD) (X Y : D) :
    (tensorC.obj (R.obj X)).obj (R.obj Y) ⟶
      R.obj ((tensorD.obj X).obj Y) :=
  M.adjunction.relativeDerivedCupProduct tensorC tensorD
    (fun A B => (M.comparison A B).hom) X Y

/-- The modeled cup product is characterized by its adjoint-side morphism. -/
@[stacks 0B68 "modeled relative cup-product specification"]
theorem cupProduct_spec (M : TensorModel R tensorC tensorD) (X Y : D) :
    (M.adjunction.homEquiv
        ((tensorC.obj (R.obj X)).obj (R.obj Y)) ((tensorD.obj X).obj Y)).symm
        (M.cupProduct X Y) =
      M.cupProductAdjoint X Y := sorry

end TensorModel

end CategoryTheory.Adjunction
