/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.LocallyOfFiniteType
public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Tensor powers of schemes over a field

This module records that cartesian-monoidal tensor powers of locally finite type schemes over a
field remain locally of finite type.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The cartesian-monoidal unit of schemes over a field is locally of finite type over that
field. -/
instance tensorUnit_locallyOfFiniteType
    {k : Type u} [Field k] :
    LocallyOfFiniteType (𝟙_ (SchemeOverField k)).hom := sorry

/-- The cartesian-monoidal tensor product of two schemes locally of finite type over a field
remains locally of finite type. -/
instance tensorProduct_locallyOfFiniteType
    {k : Type u} [Field k] (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (X ⊗ Y).hom := sorry

/-- Tensor powers of a scheme locally of finite type over a field remain locally of finite type. -/
instance tensorPower_locallyOfFiniteType
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (n : ℕ) : LocallyOfFiniteType (tensorPower X n).hom := sorry

end AlgebraicGeometry.SchemeOverField
