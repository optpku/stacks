/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor.Functor
public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Linear
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.SerreFunctor.Property
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

/-- The proper dualizing complex of a proper Gorenstein scheme over a field is perfect. -/
theorem isPerfect
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [Scheme.Gorenstein X.left] :
    RingedSpace.ModuleDerived.IsPerfect
      (properDualizingComplex X.hom).obj := sorry

/-- Fixed-left derived tensoring by the proper dualizing complex preserves perfect objects. -/
theorem tensorFunctor_mapsToPerfect
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [Scheme.Gorenstein X.left]
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (hK : RingedSpace.ModuleDerived.IsPerfect K) :
    RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.ModuleDerived.derivedTensorLeft
        (properDualizingComplex X.hom).obj).obj K) := sorry

/-- The endofunctor of perfect derived modules given by tensoring on the left with the proper
dualizing complex. -/
noncomputable def tensorFunctor
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [Scheme.Gorenstein X.left] :
    @RingedSpace.ModuleDerived.Perfect X.left.toRingedSpace ⥤
      @RingedSpace.ModuleDerived.Perfect X.left.toRingedSpace :=
  ObjectProperty.FullSubcategory.restrict
    (RingedSpace.ModuleDerived.derivedTensorLeft (properDualizingComplex X.hom).obj)
    (tensorFunctor_mapsToPerfect X)

/-- The object action of `tensorFunctor` is the canonical derived tensor action on the underlying
derived module. -/
theorem tensorFunctor_obj
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [Scheme.Gorenstein X.left]
    (K : @RingedSpace.ModuleDerived.Perfect X.left.toRingedSpace) :
    ((tensorFunctor X).obj K).obj =
      (RingedSpace.ModuleDerived.derivedTensorLeft
        (properDualizingComplex X.hom).obj).obj K.obj := sorry

/-- Tensoring perfect derived modules by the proper dualizing complex is an equivalence. -/
instance tensorFunctor_isEquivalence
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [Scheme.Gorenstein X.left] :
    (tensorFunctor X).IsEquivalence := sorry

/-- The proper dualizing-complex tensor endofunctor is a Serre functor on perfect derived
modules. -/
theorem tensorFunctor_isSerre
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [Scheme.Gorenstein X.left] :
    Functor.IsSerreWith
      (Scheme.ModuleDerived.Perfect.linearFor X.hom) (tensorFunctor X) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

end
