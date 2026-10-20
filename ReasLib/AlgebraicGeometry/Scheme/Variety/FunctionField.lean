/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.RationalMap.ComponentStalk
public import ReasLib.AlgebraicGeometry.Scheme.Variety.RationalMap
public import ReasLib.FieldTheory.Extension.Category

/-!
# Function fields of varieties and finitely generated extensions

This file relates varieties with dominant rational maps to finitely generated
field extensions through the function-field construction.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/- The function field carrier and the carrier of its bundled `CommAlgCat` object
   have the same ring operations; this identity equivalence transfers the field
   predicate to the bundled ring instance. -/
theorem functionFieldCommAlg_isField (X : SchemeOverField k) [Variety X] :
    IsField (↑(functionFieldCommAlg X)) := by
  let e : (↑(functionFieldCommAlg X)) ≃+* X.left.functionField :=
    { toFun := id
      invFun := id
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_mul' := by intro x y; rfl
      map_add' := by intro x y; rfl }
  exact e.toMulEquiv.isField (Field.toIsField _)

end AlgebraicGeometry.SchemeOverField

namespace AlgebraicGeometry.VarietyDominantRationalMapCat

variable {k : Type u} [Field k]

/-- The function field of a variety, equipped with its finite-generation property. -/
noncomputable def functionFieldCatObject (X : VarietyDominantRationalMapCat k) :
    FinitelyGeneratedFieldExtension.Cat.{u, u} k :=
  ⟨SchemeOverField.functionFieldCommAlg X.obj,
    ⟨SchemeOverField.functionFieldCommAlg_isField X.obj,
      SchemeOverField.functionField_essFiniteType X.obj⟩⟩

/- The closed point of the source function-field spectrum is sent to the generic point. -/
theorem fromFunctionField_closedPoint_eq_genericPoint
    {X Y : VarietyDominantRationalMapCat k} (f : Hom X Y) :
    f.1.fromFunctionField (IsLocalRing.closedPoint X.obj.left.functionField) =
      genericPoint Y.obj.left := sorry

/-- The `k`-algebra map on function fields induced contravariantly by a dominant rational map. -/
noncomputable def functionFieldMap {X Y : VarietyDominantRationalMapCat k} (f : Hom X Y) :
    SchemeOverField.functionFieldCommAlg Y.obj ⟶
      SchemeOverField.functionFieldCommAlg X.obj :=
  -- Local instance justification (proof-local temporary data): the source and target
  -- `CommAlgCat` maps need their canonical `k`-algebra structures only while this map is built.
  letI := SchemeOverField.functionFieldAlgebra X.obj
  -- Local instance justification (proof-local temporary data): the source and target
  -- `CommAlgCat` maps need their canonical `k`-algebra structures only while this map is built.
  letI := SchemeOverField.functionFieldAlgebra Y.obj
  CommAlgCat.ofHom {
    toRingHom :=
      ((Y.obj.left.presheaf.stalkCongr
          (.of_eq (fromFunctionField_closedPoint_eq_genericPoint f).symm)).hom ≫
        Scheme.stalkClosedPointTo f.1.fromFunctionField).hom
    commutes' := by sorry
  }

/- The map on a rational map is the corresponding pullback on function fields. -/
@[simp]
theorem functionFieldMap_hom {X Y : VarietyDominantRationalMapCat k} (f : Hom X Y) :
    (functionFieldMap f).hom.toRingHom =
      ((Y.obj.left.presheaf.stalkCongr
          (.of_eq (fromFunctionField_closedPoint_eq_genericPoint f).symm)).hom ≫
        Scheme.stalkClosedPointTo f.1.fromFunctionField).hom :=
  rfl

/- The contravariant function-field functor on varieties and dominant rational maps. -/
noncomputable def functionFieldFunctor : VarietyDominantRationalMapCat k ⥤
    (FinitelyGeneratedFieldExtension.Cat.{u, u} k)ᵒᵖ where
  obj X := Opposite.op (functionFieldCatObject X)
  map f :=
    (ObjectProperty.homMk
      (X := functionFieldCatObject _) (Y := functionFieldCatObject _)
      (functionFieldMap f)).op
  map_id := by intros; sorry
  map_comp := by intros; sorry

@[simp]
theorem functionFieldFunctor_obj (X : VarietyDominantRationalMapCat k) :
    (functionFieldFunctor.obj X).unop = functionFieldCatObject X :=
  rfl

@[simp]
theorem functionFieldFunctor_map {X Y : VarietyDominantRationalMapCat k} (f : X ⟶ Y) :
    (functionFieldFunctor.map f).unop.hom = functionFieldMap f :=
  rfl

/- The affine-model construction proves essential surjectivity and full faithfulness. -/
theorem functionFieldFunctor_isEquivalence :
    (functionFieldFunctor (k := k)).IsEquivalence := sorry

/-- The affine scheme over `k` obtained from the finite-type subalgebra selected inside a
finitely generated field extension. -/
noncomputable def affineModel (K : FinitelyGeneratedFieldExtension.Cat.{u, u} k) :
    SchemeOverField k :=
  let A : Subalgebra k K.obj :=
    @Algebra.EssFiniteType.subalgebra k K.obj _ _ _ K.property.2
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))

/-- The affine model of a finitely generated field extension is a variety over `k`. -/
theorem affineModel_isVariety (K : FinitelyGeneratedFieldExtension.Cat.{u, u} k) :
    Variety (affineModel K) := sorry

/-- The affine model, bundled as an object of the dominant rational-map category. -/
noncomputable def affineModelObject (K : FinitelyGeneratedFieldExtension.Cat.{u, u} k) :
    VarietyDominantRationalMapCat k :=
  ⟨affineModel K, affineModel_isVariety K⟩

/-- The function field of the affine model is isomorphic, as a `k`-algebra, to the given
finitely generated field extension. -/
theorem functionField_affineModel_equiv (K : FinitelyGeneratedFieldExtension.Cat.{u, u} k) :
    Nonempty
      (SchemeOverField.functionFieldCommAlg (affineModelObject K).obj ≅ K.obj) := sorry

end AlgebraicGeometry.VarietyDominantRationalMapCat
