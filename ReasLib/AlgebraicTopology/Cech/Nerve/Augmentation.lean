module

public import ReasLib.AlgebraicTopology.Cech.Nerve.Coskeletal
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 018J

# Factoring an augmentation through its Cech nerve

The bundled factorization identifies the unit of `cechNerveAdjunction`.  The fixed-augmentation
map needs only one Cech nerve and is assembled from two independent APIs: the augmentation's
compatible identity zero-simplex and reconstruction from compatible Cech zero-simplex data.
Thus the raw source-facing map shares the classifier used by the general coskeletality theorem
instead of repeating its degreewise wide-pullback construction.
-/

@[expose] public section

open CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- Cech-nerve availability for a raw augmentation is inherited by its canonical bundled form.
This instance keeps the transparent `Augmentation.toAugmented` bridge usable by typeclass search,
despite `Augmented.toArrow` being intentionally opaque to definitional equality. -/
@[stacks 018J "Cech-nerve existence for a bundled raw augmentation"]
instance Augmentation.toAugmented.hasCechNerve {X : C} {V : SimplicialObject C}
    {epsilon : V ⟶ (const C).obj X}
    [(Arrow.mk (epsilon.app (op ⦋0⦌))).HasCechNerve] :
    (Augmented.toArrow.obj (Augmentation.toAugmented epsilon)).HasCechNerve := sorry

namespace Augmented.Cech

section Core

variable (E : SimplicialObject.Augmented C)
variable [(Augmented.toArrow.obj E).HasCechNerve]

/-- Every bundled vertex map followed by the degree-zero augmentation is the augmentation in that
simplicial degree. -/
@[stacks 018J "bundled Cech projection formula"]
theorem projection
    (n : SimplexCategoryᵒᵖ) (i : Fin (unop n).len.succ) :
    E.left.map (SimplexCategory.const ⦋0⦌ (unop n) i).op ≫ E.hom.app (op ⦋0⦌) =
      E.hom.app n := sorry

/-- The degreewise map underlying the bundled fixed-arrow Cech factorization. -/
@[stacks 018J "bundled degreewise augmentation-to-Cech-nerve map"]
noncomputable def app (n : SimplexCategoryᵒᵖ) :
    E.left.obj n ⟶ (Augmented.toArrow.obj E).cechNerve.obj n :=
  Arrow.cechNerve.lift (Augmented.toArrow.obj E) n (E.hom.app n)
    (fun i ↦ E.left.map (SimplexCategory.const ⦋0⦌ (unop n) i).op)
    (projection E n)

/-- The base projection of the bundled degreewise Cech map is the augmentation component. -/
@[simp, stacks 018J "bundled Cech degreewise base projection"]
theorem app.base (n : SimplexCategoryᵒᵖ) :
    app E n ≫
      Arrow.cechNerve.base (Augmented.toArrow.obj E) n =
      E.hom.app n := sorry

/-- A vertex projection of the bundled degreewise Cech map is the corresponding vertex map. -/
@[simp, stacks 018J "bundled Cech degreewise vertex projection"]
theorem app.π (n : SimplexCategoryᵒᵖ) (i : Fin (unop n).len.succ) :
    app E n ≫
      Arrow.cechNerve.π (Augmented.toArrow.obj E) n i =
      E.left.map (SimplexCategory.const ⦋0⦌ (unop n) i).op := sorry

/-- The bundled degreewise Cech maps commute with all simplex operators. -/
@[stacks 018J "bundled augmentation-to-Cech-nerve component naturality"]
theorem app.naturality {m n : SimplexCategoryᵒᵖ} (phi : m ⟶ n) :
    E.left.map phi ≫ app E n =
      app E m ≫ (Augmented.toArrow.obj E).cechNerve.map phi := sorry

/-- The underlying simplicial map from a bundled augmentation to its fixed Cech nerve. -/
@[stacks 018J "bundled augmentation-to-Cech-nerve map"]
noncomputable def left :
    E.left ⟶ (Augmented.toArrow.obj E).cechNerve where
  app := app E
  naturality := fun {m n} phi ↦ app.naturality E (m := m) (n := n) phi

/-- The component of the bundled Cech map is its canonical degreewise construction. -/
@[simp, stacks 018J "bundled augmentation-to-Cech-nerve component formula"]
theorem left.app (n : SimplexCategoryᵒᵖ) :
    (left E).app n = app E n := sorry

/-- In degree zero, the bundled Cech map has identity vertex projection. -/
@[simp, stacks 018J "bundled augmentation-to-Cech-nerve degree-zero projection"]
theorem left.app_zero_π :
    (left E).app (op ⦋0⦌) ≫
      Arrow.cechNerve.π (Augmented.toArrow.obj E) (op ⦋0⦌) 0 =
      𝟙 (E.left _⦋0⦌) := sorry

end Core

end Augmented.Cech

namespace Augmentation.Cech

variable {X : C} {V : SimplicialObject C}
variable (epsilon : V ⟶ (const C).obj X)

/-- The identity of the zero-simplices satisfies the Cech compatibility relation because its
composite with the degree-zero augmentation is compatible in the sense of `Augmentation`. -/
@[stacks 018J "augmentation as compatible Cech zero-simplex data"]
theorem zeroSimplex.condition :
    V.δ 0 ≫ 𝟙 (V _⦋0⦌) ≫ (Arrow.mk (epsilon.app (op ⦋0⦌))).hom =
      V.δ 1 ≫ 𝟙 (V _⦋0⦌) ≫ (Arrow.mk (epsilon.app (op ⦋0⦌))).hom := sorry

/-- The compatible Cech zero-simplex attached to an augmentation is the identity map in degree
zero, whose composite with the underlying arrow is the augmentation datum from `018H`. -/
@[stacks 018J "augmentation compatible Cech zero-simplex"]
def zeroSimplex :
    Arrow.cechNerve.CompatibleZeroSimplex
      (Arrow.mk (epsilon.app (op ⦋0⦌))) V :=
  ⟨𝟙 _, zeroSimplex.condition epsilon⟩

/-- The map underlying the compatible Cech zero-simplex of an augmentation is the identity. -/
@[simp, stacks 018J "augmentation compatible Cech zero-simplex value"]
theorem zeroSimplex.val :
    (zeroSimplex epsilon).1 = 𝟙 (V _⦋0⦌) := sorry

/-- Composing the compatible Cech zero-simplex with its arrow recovers the compatible
augmentation datum classified in `018H`. -/
@[stacks 018J "compatible Cech datum recovers augmentation data"]
theorem zeroSimplex.toAugmentation :
    Arrow.cechNerve.CompatibleZeroSimplex.toAugmentation
        (Arrow.mk (epsilon.app (op ⦋0⦌))) (zeroSimplex epsilon) =
      CategoryTheory.SimplicialObject.Augmentation.zeroSimplex epsilon := sorry

variable [(Arrow.mk (epsilon.app (op ⦋0⦌))).HasCechNerve]

/-- Remark 14.20.4 (018J): reconstruct the canonical map to the Cech nerve from the compatible
identity zero-simplex supplied by the augmentation. -/
@[stacks 018J "canonical map from an augmentation to its Cech nerve"]
noncomputable def hom :
    V ⟶ (Arrow.mk (epsilon.app (op ⦋0⦌))).cechNerve :=
  Arrow.cechNerve.zeroSimplex.lift
    (Arrow.mk (epsilon.app (op ⦋0⦌))) (zeroSimplex epsilon)

/-- The component of the canonical Cech map is the generic reconstruction component of its
compatible identity zero-simplex. -/
@[simp, stacks 018J "augmentation-to-Cech-nerve component formula"]
theorem hom.app (n : SimplexCategoryᵒᵖ) :
    (hom epsilon).app n =
      Arrow.cechNerve.zeroSimplex.lift.component
        (Arrow.mk (epsilon.app (op ⦋0⦌))) (zeroSimplex epsilon) n := sorry

/-- A vertex projection of the canonical Cech map is the corresponding simplex vertex. -/
@[simp, stacks 018J "augmentation-to-Cech-nerve vertex projection"]
theorem hom.app_π (n : SimplexCategoryᵒᵖ) (i : Fin (unop n).len.succ) :
    (hom epsilon).app n ≫
        Arrow.cechNerve.π (Arrow.mk (epsilon.app (op ⦋0⦌))) n i =
      V.map (SimplexCategory.const ⦋0⦌ (unop n) i).op := sorry

/-- In degree zero, the fixed-arrow Cech map has identity projection. -/
@[simp, stacks 018J "Cech map degree-zero projection"]
theorem hom.app_zero_π :
    (hom epsilon).app (op ⦋0⦌) ≫
      Arrow.cechNerve.π
        (Arrow.mk (epsilon.app (op ⦋0⦌))) (op ⦋0⦌) 0 =
      𝟙 (V _⦋0⦌) := sorry

/-- Composing the fixed-arrow Cech map with the canonical augmentation recovers the original
augmentation. -/
@[simp, stacks 018J "Cech map followed by augmentation"]
theorem hom.comp_augmentation :
    hom epsilon ≫ (Arrow.mk (epsilon.app (op ⦋0⦌))).augmentedCechNerve.hom =
      epsilon := sorry

/-- The raw fixed-arrow construction agrees with the bundled construction after transparently
bundling the augmentation.  This is the bridge used when a downstream argument starts from
either the natural-transformation or the augmented-object presentation. -/
@[stacks 018J "raw and bundled augmentation-to-Cech-nerve bridge"]
theorem hom_eq_bundled :
    hom epsilon =
      Augmented.Cech.left (Augmentation.toAugmented epsilon) := sorry

end Augmentation.Cech

namespace Augmented.Cech

section Fixed

variable (E : SimplicialObject.Augmented C)
variable [(Augmented.toArrow.obj E).HasCechNerve]

/-- The underlying Cech map is compatible with the two augmentations and the identity map of the
augmentation point. -/
@[stacks 018J "Cech factorization compatibility"]
theorem lift.condition :
    left E ≫ (Augmented.toArrow.obj E).augmentedCechNerve.hom =
      E.hom ≫ (SimplicialObject.const C).map (𝟙 E.right) := sorry

/-- A bundled augmented simplicial object maps to the augmented Cech nerve of its degree-zero
arrow using only the limits needed for that one arrow. -/
@[stacks 018J "fixed-arrow bundled Cech factorization"]
noncomputable def lift :
    E ⟶ (Augmented.toArrow.obj E).augmentedCechNerve where
  left := left E
  right := 𝟙 E.right
  w := lift.condition E

/-- The simplicial part of the bundled fixed-arrow factorization. -/
@[simp, stacks 018J "bundled Cech factorization simplicial map"]
theorem lift.left : (lift E).left = left E := sorry

/-- The point map of the bundled fixed-arrow factorization is the identity. -/
@[simp, stacks 018J "bundled Cech factorization point map"]
theorem lift.right : (lift E).right = 𝟙 E.right := sorry

/-- The bundled fixed-arrow factorization computes degreewise by `Augmented.Cech.app`. -/
@[simp, stacks 018J "bundled Cech factorization component formula"]
theorem lift.left_app (n : SimplexCategoryᵒᵖ) :
    (lift E).left.app n = app E n := sorry

/-- The bundled fixed-arrow factorization recovers the original augmentation after forgetting its
point component. -/
@[simp, stacks 018J "bundled Cech factorization augmentation formula"]
theorem lift.comp_augmentation :
    (lift E).left ≫ (Augmented.toArrow.obj E).augmentedCechNerve.hom = E.hom := sorry

end Fixed

/-- Fixed-arrow Cech factorization is natural between any two augmented objects for which the
needed Cech nerves exist. -/
@[stacks 018J "fixed-arrow bundled Cech factorization naturality"]
theorem lift.naturality {E F : SimplicialObject.Augmented C}
    [(Augmented.toArrow.obj E).HasCechNerve]
    [(Augmented.toArrow.obj F).HasCechNerve] (f : E ⟶ F) :
    f ≫ lift F =
      lift E ≫ Arrow.mapAugmentedCechNerve (Augmented.toArrow.map f) := sorry

section Global

variable [∀ f : Arrow C, f.HasCechNerve]

/-- The canonical Cech-adjunction unit is the fixed-arrow bundled factorization. -/
@[stacks 018J "Cech-adjunction unit as the augmentation factorization"]
theorem unit.eq_lift (E : SimplicialObject.Augmented C) :
    (cechNerveAdjunction (C := C)).unit.app E = lift E := sorry

/-- Naturality of the canonical Cech-adjunction unit, exposed at the augmented-object layer. -/
@[stacks 018J "Cech-adjunction unit naturality"]
theorem unit.naturality {E F : SimplicialObject.Augmented C} (f : E ⟶ F) :
    f ≫ (cechNerveAdjunction (C := C)).unit.app F =
      (cechNerveAdjunction (C := C)).unit.app E ≫
        augmentedCechNerve.map (Augmented.toArrow.map f) := sorry

/-- The simplicial component of the Cech-adjunction unit has the fixed-arrow degreewise formula. -/
@[simp, stacks 018J "Cech-adjunction unit component formula"]
theorem unit.left_app (E : SimplicialObject.Augmented C) (n : SimplexCategoryᵒᵖ) :
    ((cechNerveAdjunction (C := C)).unit.app E).left.app n =
      app E n := sorry

/-- The point component of the Cech-adjunction unit is the identity. -/
@[simp, stacks 018J "Cech-adjunction unit point formula"]
theorem unit.right (E : SimplicialObject.Augmented C) :
    ((cechNerveAdjunction (C := C)).unit.app E).right = 𝟙 E.right := sorry

/-- The simplicial component of the Cech-adjunction unit recovers the original augmentation. -/
@[simp, stacks 018J "Cech-adjunction unit augmentation formula"]
theorem unit.comp_augmentation (E : SimplicialObject.Augmented C) :
    ((cechNerveAdjunction (C := C)).unit.app E).left ≫
      (Augmented.toArrow.obj E).augmentedCechNerve.hom = E.hom := sorry

end Global

end Augmented.Cech

end CategoryTheory.SimplicialObject
