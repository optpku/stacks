/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation.Zero
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.Zero
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero-truncated simplicial objects

A zero-truncated simplicial object is a diagram on the zero-truncated simplex category and is
therefore determined by its value at the zero simplex.  This file packages evaluation and the
constant-diagram inverse as a concrete equivalence, then compares evaluation after truncation with
ordinary degree-zero evaluation.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

/-- Evaluation of a zero-truncated simplicial object at its unique zero simplex. -/
@[stacks 0182 "evaluation of a zero-truncated simplicial object"]
abbrev evalZero : SimplicialObject.Truncated C 0 ⥤ C :=
  (evaluation (SimplexCategory.Truncated 0)ᵒᵖ C).obj
    (op (⦋0⦌₀ : SimplexCategory.Truncated 0))

/-- The constant zero-truncated simplicial object functor. -/
@[stacks 0182 "constant zero-truncated simplicial object"]
abbrev constZero : C ⥤ SimplicialObject.Truncated C 0 :=
  Functor.const (SimplexCategory.Truncated 0)ᵒᵖ

/-- Zero-truncated evaluation returns the value at the zero simplex. -/
@[simp, stacks 0182 "zero-truncated evaluation on objects"]
theorem evalZero.obj (U : SimplicialObject.Truncated C 0) :
    (evalZero (C := C)).obj U =
      U.obj (op (⦋0⦌₀ : SimplexCategory.Truncated 0)) := sorry

/-- Zero-truncated evaluation sends a natural transformation to its zero component. -/
@[simp, stacks 0182 "zero-truncated evaluation on morphisms"]
theorem evalZero.map {U V : SimplicialObject.Truncated C 0} (f : U ⟶ V) :
    (evalZero (C := C)).map f =
      f.app (op (⦋0⦌₀ : SimplexCategory.Truncated 0)) := sorry

/-- A constant zero-truncated simplicial object has its prescribed value at every object. -/
@[simp, stacks 0182 "constant zero-truncated object formula"]
theorem constZero.obj_obj (X : C) (Delta : (SimplexCategory.Truncated 0)ᵒᵖ) :
    ((constZero (C := C)).obj X).obj Delta = X := sorry

/-- A constant zero-truncated morphism has the prescribed component at every object. -/
@[simp, stacks 0182 "constant zero-truncated morphism formula"]
theorem constZero.map_app {X Y : C} (f : X ⟶ Y)
    (Delta : (SimplexCategory.Truncated 0)ᵒᵖ) :
    ((constZero (C := C)).map f).app Delta = f := sorry

/-- The objectwise canonical zero comparison is natural in the zero-truncated simplex. -/
theorem zeroUnitApp.naturality (U : SimplicialObject.Truncated C 0)
    {Delta Delta' : (SimplexCategory.Truncated 0)ᵒᵖ} (f : Delta ⟶ Delta') :
    U.map f ≫
        (U.mapIso (SimplexCategory.Truncated.zeroIso Delta'.unop).op).hom =
      (U.mapIso (SimplexCategory.Truncated.zeroIso Delta.unop).op).hom ≫
        ((constZero (C := C)).obj ((evalZero (C := C)).obj U)).map f := sorry

/-- A zero-truncated simplicial object is canonically isomorphic to the constant diagram on its
zero-simplex value.  Each component is the image of the explicit zero-simplex isomorphism. -/
@[stacks 0182 "zero-truncated object as a constant diagram"]
noncomputable def zeroUnitApp (U : SimplicialObject.Truncated C 0) :
    U ≅ (constZero (C := C)).obj ((evalZero (C := C)).obj U) :=
  NatIso.ofComponents
    (fun Delta ↦ U.mapIso (SimplexCategory.Truncated.zeroIso Delta.unop).op)
    (zeroUnitApp.naturality U)

/-- The component of the zero-truncated constant-diagram comparison is induced by the canonical
isomorphism to the zero simplex. -/
@[simp, stacks 0182 "zero-truncated constant comparison component"]
theorem zeroUnitApp_app (U : SimplicialObject.Truncated C 0)
    (Delta : (SimplexCategory.Truncated 0)ᵒᵖ) :
    (zeroUnitApp U).app Delta =
      U.mapIso (SimplexCategory.Truncated.zeroIso Delta.unop).op := sorry

/-- The forward component of the canonical constant-diagram comparison. -/
@[simp, stacks 0182 "zero-truncated constant comparison forward component"]
theorem zeroUnitApp_hom_app (U : SimplicialObject.Truncated C 0)
    (Delta : (SimplexCategory.Truncated 0)ᵒᵖ) :
    (zeroUnitApp U).hom.app Delta =
      U.map (((SimplexCategory.Truncated.zeroIso Delta.unop).op).hom) := sorry

/-- The inverse component of the canonical constant-diagram comparison. -/
@[simp, stacks 0182 "zero-truncated constant comparison inverse component"]
theorem zeroUnitApp_inv_app (U : SimplicialObject.Truncated C 0)
    (Delta : (SimplexCategory.Truncated 0)ᵒᵖ) :
    (zeroUnitApp U).inv.app Delta =
      U.map (((SimplexCategory.Truncated.zeroIso Delta.unop).op).inv) := sorry

/-- The canonical constant-diagram comparison is natural in a zero-truncated simplicial object. -/
theorem zeroUnitIso.naturality {U V : SimplicialObject.Truncated C 0} (f : U ⟶ V) :
    f ≫ (zeroUnitApp V).hom =
      (zeroUnitApp U).hom ≫
        (evalZero (C := C) ⋙ constZero (C := C)).map f := sorry

/-- The identity on zero-truncated simplicial objects is naturally isomorphic to evaluation
followed by the constant-diagram functor. -/
@[stacks 0182 "unit isomorphism for zero-truncated evaluation"]
noncomputable def zeroUnitIso :
    𝟭 (SimplicialObject.Truncated C 0) ≅
      evalZero (C := C) ⋙ constZero (C := C) :=
  NatIso.ofComponents (fun U ↦ zeroUnitApp U) (zeroUnitIso.naturality (C := C))

/-- The component of the zero-truncated equivalence unit is the objectwise constant-diagram
comparison. -/
@[simp, stacks 0182 "zero-truncated equivalence unit component"]
theorem zeroUnitIso_app (U : SimplicialObject.Truncated C 0) :
    (zeroUnitIso (C := C)).app U = zeroUnitApp U := sorry

/-- Evaluation of a constant zero-truncated simplicial object is canonically the original
object. -/
@[stacks 0182 "counit isomorphism for zero-truncated evaluation"]
noncomputable def zeroCounitIso :
    constZero (C := C) ⋙ evalZero (C := C) ≅ 𝟭 C :=
  Functor.constCompEvaluationObj (D := C)
    (op (⦋0⦌₀ : SimplexCategory.Truncated 0))

/-- The component of the zero-truncated equivalence counit is the identity isomorphism. -/
@[simp, stacks 0182 "zero-truncated equivalence counit component"]
theorem zeroCounitIso_app (X : C) :
    (zeroCounitIso (C := C)).app X = Iso.refl X := sorry

/-- The concrete unit and counit for zero-truncated evaluation satisfy the equivalence triangle. -/
theorem zeroEquivalence.triangle (U : SimplicialObject.Truncated C 0) :
    (evalZero (C := C)).map ((zeroUnitIso (C := C)).hom.app U) ≫
        (zeroCounitIso (C := C)).hom.app ((evalZero (C := C)).obj U) =
      𝟙 ((evalZero (C := C)).obj U) := sorry

/-- Zero-truncated simplicial objects are canonically equivalent to objects of the coefficient
category.  The forward functor is zero evaluation and the inverse is the constant diagram. -/
@[stacks 0182 "equivalence of zero-truncated simplicial objects with the coefficient category"]
noncomputable def zeroEquivalence : SimplicialObject.Truncated C 0 ≌ C where
  functor := evalZero
  inverse := constZero
  unitIso := zeroUnitIso
  counitIso := zeroCounitIso
  functor_unitIso_comp := zeroEquivalence.triangle

/-- The forward functor of the zero-truncation equivalence is zero evaluation. -/
@[simp, stacks 0182 "forward functor of the zero-truncation equivalence"]
theorem zeroEquivalence_functor :
    (zeroEquivalence (C := C)).functor = evalZero (C := C) := sorry

/-- The inverse functor of the zero-truncation equivalence is the constant zero-truncated
diagram. -/
@[simp, stacks 0182 "inverse functor of the zero-truncation equivalence"]
theorem zeroEquivalence_inverse :
    (zeroEquivalence (C := C)).inverse = constZero (C := C) := sorry

/-- The componentwise identity comparison between zero evaluation after truncation and ordinary
degree-zero evaluation is natural. -/
theorem evalZero.truncationIso.naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (SimplicialObject.truncation (C := C) 0 ⋙ evalZero (C := C)).map f ≫
        𝟙 ((SimplicialObject.evalZero (C := C)).obj Y) =
      𝟙 ((SimplicialObject.evalZero (C := C)).obj X) ≫
        (SimplicialObject.evalZero (C := C)).map f := sorry

/-- Truncating at zero and then evaluating is naturally isomorphic to ordinary degree-zero
evaluation. -/
@[stacks 0182 "zero-truncation followed by zero evaluation"]
noncomputable def evalZero.truncationIso :
    SimplicialObject.truncation (C := C) 0 ⋙ evalZero (C := C) ≅
      SimplicialObject.evalZero (C := C) :=
  NatIso.ofComponents
    (fun X ↦ Iso.refl ((SimplicialObject.evalZero (C := C)).obj X))
    (evalZero.truncationIso.naturality (C := C))

/-- The comparison between zero evaluation after truncation and ordinary zero evaluation is
objectwise the identity isomorphism. -/
@[simp, stacks 0182 "zero-evaluation truncation comparison component"]
theorem evalZero.truncationIso_app (X : SimplicialObject C) :
    (evalZero.truncationIso (C := C)).app X =
      Iso.refl ((SimplicialObject.evalZero (C := C)).obj X) := sorry

end CategoryTheory.SimplicialObject.Truncated
