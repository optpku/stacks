/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.FiniteLimits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Affine
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape

/-!
# Limits in chosen pro-étale slices

Weakly étale objects of a chosen big pro-étale slice form a full subcategory
with pullbacks, equalizers, and the identity arrow as terminal object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier)

/-- Weakly étale objects of a chosen big pro-étale slice are closed under
pullbacks. -/
theorem smallObjectsIsClosedUnderPullbacks :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (smallObjects X S) WalkingCospan := sorry

/-- The canonical chosen small pro-étale carrier has pullbacks. -/
theorem smallSiteHasPullbacks : HasPullbacks (smallSite X S) := sorry

/-- The source-scheme functor from the canonical chosen small pro-étale
carrier preserves pullbacks. -/
theorem smallToSchemePreservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (smallToScheme X S) := sorry

/-- The chosen big pro-étale slice over `S` has equalizers, constructed from
slice pullbacks and the terminal object `S/S`. -/
theorem bigSiteHasEqualizers : HasEqualizers (bigSite X S) :=
  @hasEqualizers_of_hasPullbacks_and_binary_products (bigSite X S) _
    (@hasBinaryProducts_of_hasTerminal_and_pullbacks (bigSite X S) _
      (ChosenBigSite.sliceIdentityTerminal X S).hasTerminal
      (ChosenBigSite.sliceHasPullbacks X S))
    (ChosenBigSite.sliceHasPullbacks X S)

/-- The source-scheme functor from a chosen big pro-étale slice preserves
equalizers. -/
theorem bigToSchemePreservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (bigToScheme X S) := sorry

/-- Weakly étale objects of a chosen big pro-étale slice are closed under
equalizers. -/
theorem smallObjectsIsClosedUnderEqualizers :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (smallObjects X S) WalkingParallelPair := sorry

/-- The canonical chosen small pro-étale carrier has equalizers. -/
theorem smallSiteHasEqualizers : HasEqualizers (smallSite X S) := sorry

/-- The source-scheme functor from the canonical chosen small pro-étale
carrier preserves equalizers. -/
theorem smallToSchemePreservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (smallToScheme X S) := sorry

/-- The identity object `S/S` satisfies the small-site weakly étale
predicate. -/
theorem smallObjects_mk_id : smallObjects X S (Over.mk (𝟙 S)) :=
  ((X.toScheme.map_id S).symm ▸
    MorphismProperty.id_mem (@WeaklyEtale) (X.toScheme.obj S) :
      WeaklyEtale (X.toScheme.map (𝟙 S)))

/-- The identity object `S/S` as an object of the canonical chosen small
pro-étale carrier. -/
def smallTerminalObject : smallSite X S :=
  ⟨Over.mk (𝟙 S), smallObjects_mk_id X S⟩

/-- The canonical morphism from a chosen small pro-étale object to `S/S`. -/
def smallTerminalFrom (U : smallSite X S) :
    U ⟶ smallTerminalObject X S :=
  ObjectProperty.homMk (Over.homMk U.obj.hom (Category.comp_id _))

/-- Every morphism from a chosen small pro-étale object to `S/S` is the
canonical one. -/
theorem smallTerminalFrom_unique (U : smallSite X S)
    (f : U ⟶ smallTerminalObject X S) :
    f = smallTerminalFrom X S U := sorry

/-- The identity object `S/S` is terminal in the canonical chosen small
pro-étale carrier. -/
noncomputable def smallTerminalObjectIsTerminal :
    IsTerminal (smallTerminalObject X S) :=
  IsTerminal.ofUniqueHom (smallTerminalFrom X S) (smallTerminalFrom_unique X S)

end AlgebraicGeometry.ChosenBigProetaleSite
