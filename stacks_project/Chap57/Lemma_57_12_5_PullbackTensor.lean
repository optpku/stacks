module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure
public import stacks_project.Chap57.Theorem_57_6_3_PerfectDerived

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.RingedSpace
open CategoryTheory.DerivedCategory
open AlgebraicGeometry.SchemeOverField.PerfectDerived
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- The abelian category of `𝒪_X`-modules on a scheme. -/
abbrev schemeModules (X : Scheme.{u}) := X.toRingedSpace.Modules

/-- `schemeModules` is the category of modules on the underlying ringed space. -/
theorem schemeModules_eq (X : Scheme.{u}) :
    schemeModules X = X.toRingedSpace.Modules := sorry

/-- Perfect objects of `D(𝒪_X)` for a scheme. -/
abbrev schemePerfect (X : Scheme.{u}) : ObjectProperty (ModuleDerived X.toRingedSpace) :=
  let _X : RingedSpace.{u} := X.toRingedSpace
  ModuleDerived.perfect

/-- Membership in `schemePerfect` is derived perfectness. -/
theorem schemePerfect_apply {X : Scheme.{u}} (K : ModuleDerived X.toRingedSpace) :
    schemePerfect X K ↔ ModuleDerived.IsPerfect K := sorry

/-- Unbounded complexes of scheme modules admit totalized tensor products. -/
instance instHasMapBifunctor_schemeModules (X : Scheme.{u})
    (K L : CochainComplex (schemeModules X) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (MonoidalCategory.curriedTensor (schemeModules X)) (ComplexShape.up ℤ) :=
  sorry

/-- Derived tensoring with a fixed right factor is left-derivable on scheme modules. -/
instance instDerivedTensorRightHas (X : Scheme.{u}) :
    @DerivedTensor.Right.Has (schemeModules X) _ _ _ _ _ _ := sorry

/-- A scheme endomorphism induces the identity on the underlying topological space. -/
abbrev IsIdentityOnUnderlyingSpace {X : Scheme.{u}} (f : X ⟶ X) : Prop :=
  f.base = 𝟙 X.toTopCat

/-- Unfolding of `IsIdentityOnUnderlyingSpace`. -/
theorem IsIdentityOnUnderlyingSpace.iff {X : Scheme.{u}} (f : X ⟶ X) :
    IsIdentityOnUnderlyingSpace f ↔ f.base = 𝟙 X.toTopCat := sorry

/-- Tensoring a perfect derived object with the degree-`0` image of an invertible module
remains perfect. -/
theorem tensorInvertible_le_perfect {X : Scheme.{u}} (L : X.Modules)
    [Scheme.Modules.Invertible L] :
    schemePerfect X ≤
      (schemePerfect X).inverseImage
        (DerivedTensor.Right.functor
          ((DerivedCategory.singleFunctor (schemeModules X) (0 : ℤ)).obj L)) := sorry

/-- The endofunctor `M ↦ Lf^* M ⊗^L L` of `PerfectDerived X`, for a scheme endomorphism `f`
and an invertible `𝒪_X`-module `L`. -/
noncomputable def pullbackTensorInvertible {k : Type u} [Field k] {X : SchemeOverField k}
    (f : X.left ⟶ X.left) (L : X.left.Modules) [Scheme.Modules.Invertible L] :
    PerfectDerived X ⥤ PerfectDerived X :=
  modulePullbackPerfect f.toLRSHom.toShHom ⋙
    ObjectProperty.FullSubcategory.restrict
      (DerivedTensor.Right.functor
        ((DerivedCategory.singleFunctor (schemeModules X.left) (0 : ℤ)).obj L))
      (tensorInvertible_le_perfect L)

/-- After inclusion into the ambient derived category, `pullbackTensorInvertible` is derived
pullback followed by derived tensor with the degree-`0` image of `L`. -/
theorem pullbackTensorInvertible_comp_inclusion {k : Type u} [Field k] {X : SchemeOverField k}
    (f : X.left ⟶ X.left) (L : X.left.Modules) [Scheme.Modules.Invertible L] :
    pullbackTensorInvertible f L ⋙ inclusion X =
      inclusion X ⋙
        L(f.toLRSHom.toShHom)^* ⋙
          DerivedTensor.Right.functor
            ((DerivedCategory.singleFunctor (schemeModules X.left) (0 : ℤ)).obj L) :=
  sorry

/-- Objectwise, `pullbackTensorInvertible` is derived pullback followed by derived tensor
with the degree-`0` image of `L`. -/
theorem pullbackTensorInvertible_obj {k : Type u} [Field k] {X : SchemeOverField k}
    (f : X.left ⟶ X.left) (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (M : PerfectDerived X) :
    (inclusion X).obj ((pullbackTensorInvertible f L).obj M) =
      (DerivedTensor.Right.functor
        ((DerivedCategory.singleFunctor (schemeModules X.left) (0 : ℤ)).obj L)).obj
        ((L(f.toLRSHom.toShHom)^*).obj ((inclusion X).obj M)) := sorry

/-- The pullback-tensor endofunctor is `k`-linear. -/
instance instLinear_pullbackTensorInvertible {k : Type u} [Field k] {X : SchemeOverField k}
    (f : X.left ⟶ X.left) (L : X.left.Modules) [Scheme.Modules.Invertible L] :
    (pullbackTensorInvertible f L).Linear k := sorry

/-- Integer shifts commute with the pullback-tensor endofunctor on the nose. -/
theorem pullbackTensorInvertible_commShift_eq {k : Type u} [Field k] {X : SchemeOverField k}
    (f : X.left ⟶ X.left) (L : X.left.Modules) [Scheme.Modules.Invertible L] (a : ℤ) :
    shiftFunctor (PerfectDerived X) a ⋙ pullbackTensorInvertible f L =
      pullbackTensorInvertible f L ⋙ shiftFunctor (PerfectDerived X) a := sorry

/-- The pullback-tensor endofunctor commutes with integer shifts. -/
instance instCommShift_pullbackTensorInvertible {k : Type u} [Field k] {X : SchemeOverField k}
    (f : X.left ⟶ X.left) (L : X.left.Modules) [Scheme.Modules.Invertible L] :
    (pullbackTensorInvertible f L).CommShift ℤ where
  commShiftIso a := eqToIso (pullbackTensorInvertible_commShift_eq f L a)
  commShiftIso_zero := sorry
  commShiftIso_add := sorry

/-- The pullback-tensor endofunctor is exact as a triangulated functor. -/
theorem pullbackTensorInvertible_hasTriangulatedStructure {k : Type u} [Field k]
    {X : SchemeOverField k} (f : X.left ⟶ X.left) (L : X.left.Modules)
    [Scheme.Modules.Invertible L] :
    (pullbackTensorInvertible f L).HasTriangulatedStructure := sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
