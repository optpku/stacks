module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.CategoryTheory.Monoidal.Duality.Comparison
public import ReasLib.CategoryTheory.Monoidal.Duality.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Duality.Functor

/-!
# Tensor inverses as exact pairings

Two-sided tensor-inverse isomorphisms canonically determine exact-pairing data. This identifies
the chosen inverse of an invertible object with every other right dual and supplies coherent
comparisons for the unit, tensor products, and strong monoidal functors.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

noncomputable section

universe v u vD uD

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency false

namespace ExactPairing

namespace TensorInverse

/-- The triangle defect of two specified tensor-inverse isomorphisms, viewed as an automorphism
of the original object.  Normalizing by this automorphism is what turns arbitrary two-sided
inverse data into coherent duality data. -/
def defect {X Y : C} (right : X ⊗ Y ≅ 𝟙_ C) (left : Y ⊗ X ≅ 𝟙_ C) : X ≅ X :=
  (λ_ X).symm ≪≫ (right.symm ⊗ᵢ Iso.refl X) ≪≫
    α_ X Y X ≪≫ (Iso.refl X ⊗ᵢ left) ≪≫ ρ_ X

/-- The evaluation obtained by correcting a specified left tensor-inverse comparison by the
triangle defect of the two inverse isomorphisms. -/
def evaluation {X Y : C} (right : X ⊗ Y ≅ 𝟙_ C)
    (left : Y ⊗ X ≅ 𝟙_ C) : Y ⊗ X ⟶ 𝟙_ C :=
  (Iso.refl Y ⊗ᵢ (defect right left).symm).hom ≫ left.hom

/-- The forward map of the triangle defect is the unnormalized snake composite. -/
theorem defect_hom {X Y : C} (right : X ⊗ Y ≅ 𝟙_ C)
    (left : Y ⊗ X ≅ 𝟙_ C) :
    (defect right left).hom =
      (λ_ X).inv ≫ right.inv ▷ X ≫ (α_ X Y X).hom ≫
        X ◁ left.hom ≫ (ρ_ X).hom := by
  simp [defect]

/-- The normalized evaluation satisfies the snake identity on the original object. -/
theorem evaluation_coevaluation {X Y : C} (right : X ⊗ Y ≅ 𝟙_ C)
    (left : Y ⊗ X ≅ 𝟙_ C) :
    right.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ evaluation right left =
      (λ_ X).hom ≫ (ρ_ X).inv := by
  have h_assoc (d : X ⟶ X) :
      (X ⊗ Y) ◁ d ≫ (α_ X Y X).hom =
        (α_ X Y X).hom ≫ X ◁ Y ◁ d := by
    simp
  have h_slide (d : X ⟶ X) :
      right.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ Y ◁ d =
        (𝟙_ C) ◁ d ≫ right.inv ▷ X ≫ (α_ X Y X).hom := by
    rw [← h_assoc]
    rw [← whisker_exchange_assoc]
  dsimp [evaluation]
  simp only [Iso.symm_hom, tensorIso_hom, Iso.refl_hom]
  calc
    _ = (λ_ X).hom ≫ (defect right left).inv ≫
        (defect right left).hom ≫ (ρ_ X).inv := by
      rw [defect_hom]
      rw [id_tensorHom, whiskerLeft_comp]
      rw [Category.assoc, reassoc_of% (h_slide (defect right left).inv)]
      simp only [Category.assoc, id_whiskerLeft, Iso.hom_inv_id, Category.comp_id]
    _ = _ := by
      rw [Iso.inv_hom_id_assoc]

/-- The normalized evaluation satisfies the snake identity on the tensor inverse. -/
theorem coevaluation_evaluation {X Y : C} (right : X ⊗ Y ≅ 𝟙_ C)
    (left : Y ⊗ X ≅ 𝟙_ C) :
    Y ◁ right.inv ≫ (α_ Y X Y).inv ≫ evaluation right left ▷ Y =
      (ρ_ Y).hom ≫ (λ_ Y).inv := by
  let evaluationIso : Y ⊗ X ≅ 𝟙_ C :=
    (Iso.refl Y ⊗ᵢ (defect right left).symm) ≪≫ left
  let unitNatIso : 𝟭 C ≅ tensorRight X ⋙ tensorRight Y :=
    (rightUnitorNatIso C).symm ≪≫
      (tensoringRight C).mapIso right.symm ≪≫ tensorRightTensor X Y
  let counitNatIso : tensorRight Y ⋙ tensorRight X ≅ 𝟭 C :=
    (tensorRightTensor Y X).symm ≪≫
      (tensoringRight C).mapIso evaluationIso ≪≫ rightUnitorNatIso C
  have h_functor_triangle (Z : C) :
      (tensorRight X).map (unitNatIso.hom.app Z) ≫
          counitNatIso.hom.app ((tensorRight X).obj Z) =
        𝟙 ((tensorRight X).obj Z) := by
    simp [unitNatIso, counitNatIso, evaluationIso]
    change _ = 𝟙 (Z ⊗ X)
    calc
      _ = 𝟙 (Z ⊗ X) ⊗≫ Z ◁
          (right.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ evaluation right left) ⊗≫
            𝟙 (Z ⊗ X) := by
        dsimp [evaluation]
        simp only [Iso.symm_hom, tensorIso_hom, Iso.refl_hom]
        monoidal
      _ = 𝟙 (Z ⊗ X) ⊗≫ Z ◁ ((λ_ X).hom ≫ (ρ_ X).inv) ⊗≫
          𝟙 (Z ⊗ X) := by
        rw [evaluation_coevaluation]
      _ = 𝟙 (Z ⊗ X) := by
        monoidal
  let e : C ≌ C :=
    { functor := tensorRight X
      inverse := tensorRight Y
      unitIso := unitNatIso
      counitIso := counitNatIso
      functor_unitIso_comp := h_functor_triangle }
  let a : 𝟙_ C ⊗ Y ⟶ 𝟙_ C ⊗ Y :=
    unitNatIso.hom.app (𝟙_ C ⊗ Y) ≫
      (tensorRight Y).map (counitNatIso.hom.app (𝟙_ C))
  have h := e.unit_inverse_comp (𝟙_ C)
  change a = 𝟙 (𝟙_ C ⊗ Y) at h
  calc
    _ = ((ρ_ Y).hom ≫ (λ_ Y).inv) ≫ a := by
      simp [a, unitNatIso, counitNatIso, evaluationIso, evaluation]
      monoidal
    _ = _ := by
      rw [h, Category.comp_id]

end TensorInverse

/-- Two-sided tensor-inverse isomorphisms determine an exact pairing after canonically
normalizing the evaluation by their triangle defect. -/
@[stacks 0FFN "exact pairing from a tensor inverse", implicit_reducible]
def ofTensorInverse {X Y : C} (right : X ⊗ Y ≅ 𝟙_ C)
    (left : Y ⊗ X ≅ 𝟙_ C) : ExactPairing X Y where
  coevaluation' := right.inv
  evaluation' := TensorInverse.evaluation right left
  coevaluation_evaluation' := TensorInverse.coevaluation_evaluation right left
  evaluation_coevaluation' := TensorInverse.evaluation_coevaluation right left

/-- The coevaluation of the pairing defined by tensor-inverse isomorphisms is the inverse of
the right tensor comparison. -/
@[simp]
theorem ofTensorInverse.coevaluation {X Y : C} (right : X ⊗ Y ≅ 𝟙_ C)
    (left : Y ⊗ X ≅ 𝟙_ C) :
    (ofTensorInverse right left).coevaluation' = right.inv := rfl

/-- The evaluation of the pairing defined by tensor-inverse isomorphisms is the normalized left
tensor comparison. -/
@[simp]
theorem ofTensorInverse.evaluation {X Y : C} (right : X ⊗ Y ≅ 𝟙_ C)
    (left : Y ⊗ X ≅ 𝟙_ C) :
    (ofTensorInverse right left).evaluation' =
      TensorInverse.evaluation right left := rfl

end ExactPairing

namespace MonoidalCategory.isInvertibleObject

/-- The chosen tensor inverse of an invertible object forms a canonical exact pairing with the
object. -/
@[stacks 0FFN "canonical pairing with the chosen inverse", implicit_reducible]
def exactPairing (X : C) [isInvertibleObject X] : ExactPairing X (inverse X) :=
  ExactPairing.ofTensorInverse (tensorInverseIso X) (inverseTensorIso X)

/-- The chosen tensor inverse also pairs with the original object in the reverse order.  This is
the canonical exact pairing exhibiting the original object as a left dual. -/
@[implicit_reducible]
def inverseExactPairing (X : C) [isInvertibleObject X] : ExactPairing (inverse X) X :=
  ExactPairing.ofTensorInverse (inverseTensorIso X) (tensorInverseIso X)

/-- Every tensor-invertible object is right-dualizable. -/
@[stacks 0FFN "invertible implies right-dualizable",
  stacks 0FPG "invertible implies dualizable"]
theorem isRightDualizable (X : C) [isInvertibleObject X] :
    IsRightDualizable X :=
  IsRightDualizable.of_exactPairing (exactPairing X)

/-- Every tensor-invertible object is left-dualizable. -/
@[stacks 0FFN "invertible implies left-dualizable"]
theorem isLeftDualizable (X : C) [isInvertibleObject X] :
    IsLeftDualizable X :=
  IsLeftDualizable.of_exactPairing (inverseExactPairing X)

/-- The canonical invertible-object pairing has the inverse of `tensorInverseIso` as its
coevaluation. -/
@[simp]
theorem exactPairing.coevaluation (X : C) [isInvertibleObject X] :
    (exactPairing X).coevaluation' = (tensorInverseIso X).inv := rfl

/-- The canonical invertible-object pairing uses the normalized evaluation attached to its two
tensor-inverse comparisons. -/
@[simp]
theorem exactPairing.evaluation (X : C) [isInvertibleObject X] :
    (exactPairing X).evaluation' =
      ExactPairing.TensorInverse.evaluation
        (tensorInverseIso X) (inverseTensorIso X) := rfl

/-- Any explicit right dual of an invertible object is canonically isomorphic to its chosen
tensor inverse. -/
def inverseIso (X : C) [isInvertibleObject X] {Y : C}
    (p : ExactPairing X Y) : Y ≅ inverse X :=
  rightDualIso p (exactPairing X)

/-- The canonical comparison from an explicit right dual to the chosen inverse preserves both
pairing maps. -/
theorem inverseIso.isCompatible (X : C) [isInvertibleObject X] {Y : C}
    (p : ExactPairing X Y) :
    ExactPairing.RightDualIso p (exactPairing X) (inverseIso X p) :=
  ExactPairing.rightDualIso.isCompatible p (exactPairing X)

/-- The canonical comparison to the chosen inverse carries the supplied coevaluation to the
canonical tensor-inverse coevaluation. -/
@[reassoc (attr := simp)]
theorem inverseIso.coevaluation (X : C) [isInvertibleObject X] {Y : C}
    (p : ExactPairing X Y) :
    p.coevaluation' ≫ X ◁ (inverseIso X p).hom = (tensorInverseIso X).inv := by
  rw [(inverseIso.isCompatible X p).coevaluation,
    exactPairing.coevaluation]

/-- The canonical comparison to the chosen inverse carries the canonical normalized evaluation
to the supplied evaluation. -/
@[reassoc (attr := simp)]
theorem inverseIso.evaluation (X : C) [isInvertibleObject X] {Y : C}
    (p : ExactPairing X Y) :
    (inverseIso X p).hom ▷ X ≫ (exactPairing X).evaluation' =
      p.evaluation' :=
  (inverseIso.isCompatible X p).evaluation

/-- A pairing-preserving comparison from an explicit right dual to the chosen inverse is the
canonical comparison. -/
theorem inverseIso.eq_of_compatible (X : C) [isInvertibleObject X] {Y : C}
    (p : ExactPairing X Y) (i : Y ≅ inverse X)
    (hi : ExactPairing.RightDualIso p (exactPairing X) i) :
    i = inverseIso X p :=
  ExactPairing.rightDualIso.eq_of_compatible p (exactPairing X) i hi

/-- The chosen inverse of the monoidal unit is canonically isomorphic to the unit. -/
def inverseUnitIso : inverse (𝟙_ C) ≅ 𝟙_ C :=
  rightDualIso (exactPairing (𝟙_ C))
    (inferInstance : ExactPairing (𝟙_ C) (𝟙_ C))

/-- The comparison between the chosen inverse of the unit and the unit preserves their exact
pairings. -/
theorem inverseUnitIso.isCompatible :
    ExactPairing.RightDualIso (exactPairing (𝟙_ C))
      (inferInstance : ExactPairing (𝟙_ C) (𝟙_ C))
      (inverseUnitIso (C := C)) :=
  ExactPairing.rightDualIso.isCompatible _ _

/-- Tensoring the canonical pairings of two invertible objects gives the canonical explicit
right-dual pairing for their tensor product. -/
@[implicit_reducible]
def tensorExactPairing (X Y : C) [isInvertibleObject X] [isInvertibleObject Y] :
    ExactPairing (X ⊗ Y) (inverse Y ⊗ inverse X) :=
  @ExactPairing.tensor C _ _ X Y (inverse X) (inverse Y)
    (exactPairing X) (exactPairing Y)

/-- The chosen inverse of a tensor product is canonically the reversed tensor product of the
chosen inverses. -/
def inverseTensorProductIso (X Y : C) [isInvertibleObject X] [isInvertibleObject Y] :
    inverse (X ⊗ Y) ≅ inverse Y ⊗ inverse X :=
  rightDualIso (exactPairing (X ⊗ Y)) (tensorExactPairing X Y)

/-- The tensor-product comparison of chosen inverses preserves the canonical exact pairings. -/
theorem inverseTensorProductIso.isCompatible
    (X Y : C) [isInvertibleObject X] [isInvertibleObject Y] :
    ExactPairing.RightDualIso (exactPairing (X ⊗ Y)) (tensorExactPairing X Y)
      (inverseTensorProductIso X Y) :=
  ExactPairing.rightDualIso.isCompatible _ _

variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]

/-- A strong monoidal functor carries a chosen inverse to an object canonically isomorphic to
the chosen inverse of the image. -/
def mapInverseIso (F : C ⥤ D) [F.Monoidal] (X : C) [isInvertibleObject X] :
    inverse (F.obj X) ≅ F.obj (inverse X) :=
  rightDualIso (exactPairing (F.obj X)) ((exactPairing X).map F)

/-- The strong-monoidal comparison of chosen inverses preserves the canonical image pairing. -/
theorem mapInverseIso.isCompatible (F : C ⥤ D) [F.Monoidal]
    (X : C) [isInvertibleObject X] :
    ExactPairing.RightDualIso (exactPairing (F.obj X)) ((exactPairing X).map F)
      (mapInverseIso F X) :=
  ExactPairing.rightDualIso.isCompatible _ _



end MonoidalCategory.isInvertibleObject

end CategoryTheory
