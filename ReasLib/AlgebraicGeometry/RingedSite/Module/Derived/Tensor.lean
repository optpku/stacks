module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor

/-!
# Derived tensor products of module sheaves on ringed sites

The ordinary tensor product on module sheaves is the canonical symmetric monoidal source for
derived tensoring.  This file owns the existence interface; downstream files use the generic
`DerivedTensor` construction and do not choose K-flat representatives or local instances.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

-- Local instance justification (defeq pin): tensor uses the same canonical derived category as the ringed-site localization, without a new global registration.
attribute [local instance] moduleCategoryHasDerivedCategory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (O : Sheaf J CommRingCat.{w})

/-- The total tensor product of two unbounded complexes of module sheaves exists canonically. -/
@[stacks 06YU "complex tensor totalization"]
theorem moduleCategoryHasMapBifunctor
    (K L : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (ringedSiteModuleCategory.{u, v, w, w} J O)) (up ℤ) := sorry

/-- The canonical tensor product of module sheaves admits unbounded fixed-left and fixed-right
derived tensor functors. -/
@[stacks 06YU]
theorem moduleCategoryHasDerivedTensor :
    @DerivedCategory.DerivedTensor.Has
      (ringedSiteModuleCategory.{u, v, w, w} J O) _ _ _ _ _
      (moduleCategoryHasMapBifunctor O) := sorry

variable {O}

/-- The canonical fixed-left derived tensor functor on derived module sheaves over a ringed
site. -/
def derivedTensorLeft (K : RingedSiteDerived J O) :
    RingedSiteDerived J O ⥤ RingedSiteDerived J O :=
  @DerivedCategory.DerivedTensor.Left.functor
    (ringedSiteModuleCategory.{u, v, w, w} J O) _ _ _ _ _
    (moduleCategoryHasMapBifunctor O) K (moduleCategoryHasDerivedTensor O).left

end

end SheafOfModules.RingedSite
