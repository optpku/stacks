module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Evaluation
public import ReasLib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MB

# Pointwise monoidal structure on cosimplicial objects

Mathlib keeps `CosimplicialObject` as an opaque wrapper around a functor category.  The ordinary
functor-category monoidal instances therefore do not reach its public type automatically.  This
leaf exposes the canonical pointwise tensor and its monoidal-preadditive compatibility without
introducing a second tensor model.
-/

@[expose] public section

universe v u

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A] [MonoidalCategory A]

/-- 20.25.3.2 (07MB): cosimplicial objects inherit the pointwise monoidal structure. -/
@[stacks 07MB "pointwise tensor on cosimplicial objects"]
noncomputable instance monoidal : MonoidalCategory (CosimplicialObject A) :=
  inferInstanceAs (MonoidalCategory (SimplexCategory ⥤ A))

variable [Preadditive A] [MonoidalPreadditive A]

/-- 20.25.3.2 (07MB): pointwise tensor on cosimplicial objects is monoidal-preadditive. -/
@[stacks 07MB "pointwise tensor is additive in cosimplicial objects"]
noncomputable instance monoidalPreadditive :
    MonoidalPreadditive (CosimplicialObject A) :=
  inferInstanceAs (MonoidalPreadditive (SimplexCategory ⥤ A))

end CategoryTheory.CosimplicialObject

end
