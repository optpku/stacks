module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import ReasLib.CategoryTheory.Functor.Exactness.Additive

/-!
# Faithfulness from exactness

This leaf records the kernel criterion for faithfulness of an exact functor between
abelian categories.
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory.Functor

open Abelian Limits

/-- An exact functor between abelian categories is faithful when its kernel contains only
zero objects. -/
@[stacks 06XK "zero-kernel faithfulness criterion, forward direction"]
theorem faithful_of_exact_of_kernel_le_isZero
    {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : F.kernel ≤ IsZero) :
    F.Faithful := sorry

/-- A faithful functor which preserves zero morphisms reflects zero objects. -/
@[stacks 06XK "faithful functors have zero kernel"]
theorem kernel_le_isZero_of_faithful
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {D : Type*} [Category D] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.Faithful] :
    F.kernel ≤ IsZero := sorry

/-- For an exact functor between abelian categories, faithfulness is equivalent to reflecting
zero objects. The latter condition is expressed canonically as `F.kernel ≤ IsZero`. -/
@[stacks 06XK "zero-kernel characterization of faithful exact functors"]
theorem kernel_le_isZero_iff_faithful
    {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.kernel ≤ IsZero ↔ F.Faithful := sorry

/-- Explicit-property form of `Functor.kernel_le_isZero_iff_faithful`, for callers carrying
exactness as a term rather than as preservation instances. -/
@[stacks 06XK "explicit exactness form"]
theorem kernel_le_isZero_iff_faithful_of_exact
    {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) (hF : exactFunctor C D F) :
    F.kernel ≤ IsZero ↔ F.Faithful := sorry

end CategoryTheory.Functor
