/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.TensorInvertible
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Triangulated
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.RingedSpace
open CategoryTheory.DerivedCategory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- Derived pullback along an endomorphism over the field followed by derived tensoring
with the degree-zero realization of an invertible module, restricted to perfect complexes. -/
noncomputable def pullbackTensorInvertible {k : Type u} [Field k] {X : SchemeOverField k}
    (φ : X ⟶ X) (L : X.left.Modules) [Scheme.Modules.Invertible L] :
    PerfectDerived X ⥤ PerfectDerived X :=
  modulePullbackPerfect φ.left.toLRSHom.toShHom ⋙
    ObjectProperty.FullSubcategory.restrict
      (DerivedTensor.Right.functor
        ((DerivedCategory.singleFunctor X.left.toRingedSpace.Modules (0 : ℤ)).obj L))
      (fun E (hE : ModuleDerived.IsPerfect E) => hE.tensorInvertible L)

/-- Inclusion into the ambient derived category identifies the pullback–tensor functor
with derived pullback followed by derived tensoring with the degree-zero module. -/
noncomputable def pullbackTensorInvertibleCompInclusionIso
    {k : Type u} [Field k] {X : SchemeOverField k}
    (φ : X ⟶ X) (L : X.left.Modules) [Scheme.Modules.Invertible L] :
    pullbackTensorInvertible φ L ⋙ inclusion X ≅
      inclusion X ⋙ L(φ.left.toLRSHom.toShHom)^* ⋙
        DerivedTensor.Right.functor
          ((DerivedCategory.singleFunctor X.left.toRingedSpace.Modules (0 : ℤ)).obj L) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ObjectProperty.FullSubcategory.restrict.compιIso
      (Q := ModuleDerived.perfect (X := X.left.toRingedSpace))
      (DerivedTensor.Right.functor
        ((DerivedCategory.singleFunctor X.left.toRingedSpace.Modules (0 : ℤ)).obj L))
      (fun E (hE : ModuleDerived.IsPerfect E) => hE.tensorInvertible L)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (modulePullbackPerfectCompιIso φ.left.toLRSHom.toShHom) _ ≪≫
    Functor.associator _ _ _

/-- On underlying derived objects, the pullback–tensor functor applies derived pullback
and then tensors with the degree-zero realization of the invertible module. -/
theorem pullbackTensorInvertible_obj {k : Type u} [Field k] {X : SchemeOverField k}
    (φ : X ⟶ X) (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (M : PerfectDerived X) :
    (inclusion X).obj ((pullbackTensorInvertible φ L).obj M) =
      (DerivedTensor.Right.functor
        ((DerivedCategory.singleFunctor X.left.toRingedSpace.Modules (0 : ℤ)).obj L)).obj
        ((L(φ.left.toLRSHom.toShHom)^*).obj ((inclusion X).obj M)) := sorry

/-- Pullback and tensoring along an endomorphism over the field is linear over that field. -/
instance instLinear_pullbackTensorInvertible {k : Type u} [Field k] {X : SchemeOverField k}
    (φ : X ⟶ X) (L : X.left.Modules) [Scheme.Modules.Invertible L] :
    (pullbackTensorInvertible φ L).Linear k := sorry

/-- The pullback–tensor functor has the shift comparison induced from derived pullback
and derived tensoring through the fully faithful inclusion of perfect complexes. -/
noncomputable instance instCommShift_pullbackTensorInvertible
    {k : Type u} [Field k] {X : SchemeOverField k}
    (φ : X ⟶ X) (L : X.left.Modules) [Scheme.Modules.Invertible L] :
    (pullbackTensorInvertible φ L).CommShift ℤ :=
  @Functor.CommShift.ofComp _ _ _ _ _ _ _ _ _
    (pullbackTensorInvertibleCompInclusionIso φ L) _ _ ℤ _ _ _ _ _
    (@Functor.CommShift.comp _ _ _ _ _ _ (inclusion X)
      (L(φ.left.toLRSHom.toShHom)^* ⋙ DerivedTensor.Right.functor
        ((DerivedCategory.singleFunctor X.left.toRingedSpace.Modules (0 : ℤ)).obj L))
      ℤ _ _ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ (L(φ.left.toLRSHom.toShHom)^*)
        (DerivedTensor.Right.functor
          ((DerivedCategory.singleFunctor X.left.toRingedSpace.Modules (0 : ℤ)).obj L))
        ℤ _ _ _ _
        (modulePullbackDerived.commShift φ.left.toLRSHom.toShHom)
        (DerivedTensor.Right.commShift
          ((DerivedCategory.singleFunctor X.left.toRingedSpace.Modules (0 : ℤ)).obj L))))

/-- Derived pullback followed by tensoring with an invertible module is exact on perfect
complexes. -/
theorem pullbackTensorInvertible_hasTriangulatedStructure {k : Type u} [Field k]
    {X : SchemeOverField k} (φ : X ⟶ X) (L : X.left.Modules)
    [Scheme.Modules.Invertible L] :
    (pullbackTensorInvertible φ L).HasTriangulatedStructure := sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
