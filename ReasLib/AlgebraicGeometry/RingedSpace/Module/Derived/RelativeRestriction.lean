/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

@[expose] public section

/-!
# Derived restriction to an inverse-image structure sheaf

This file defines restriction of derived module sheaves from `𝒪_X` to `f⁻¹𝒪_S` for a
morphism of ringed spaces `f : X ⟶ S`.
-/

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite (restrictionAlong)
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X S : RingedSpace.{u}}

/-- The source space equipped with the inverse-image structure sheaf `f⁻¹𝒪_S`. -/
abbrev inverseImageBase (f : X ⟶ S) : RingedSpace.{u} :=
  { carrier := X
    presheaf := ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf).presheaf
    IsSheaf := ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf).2 }

/-- The structure sheaf of `inverseImageBase f` is the inverse image of the target structure
sheaf. -/
theorem inverseImageBase_sheaf (f : X ⟶ S) :
    (inverseImageBase f).sheaf =
      (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf := sorry

end AlgebraicGeometry.RingedSpace.Hom

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X S : RingedSpace.{u}}

/-- Restriction of `𝒪_X`-modules to modules over the inverse-image sheaf `f⁻¹𝒪_S`. -/
abbrev relativeRestrictionFunctor (f : X ⟶ S) :
    X.Modules ⥤ (RingedSpace.Hom.inverseImageBase f).Modules :=
  restrictionAlong
    (J := Opens.grothendieckTopology X)
    (RingedSpace.Hom.inverseImageStructureSheafHomComm f :
      (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf ⟶ X.sheaf)

/-- On objects, `relativeRestrictionFunctor f` is the established relative-module
construction. -/
theorem relativeRestrictionFunctor_obj (f : X ⟶ S) (F : X.Modules) :
    (relativeRestrictionFunctor f).obj F = SheafOfModules.relativeModule F f := sorry

/-- Restriction to `f⁻¹𝒪_S` preserves finite limits. -/
noncomputable instance relativeRestrictionFunctor_preservesFiniteLimits (f : X ⟶ S) :
    Limits.PreservesFiniteLimits (relativeRestrictionFunctor f) := sorry

/-- Restriction to `f⁻¹𝒪_S` preserves finite colimits. -/
noncomputable instance relativeRestrictionFunctor_preservesFiniteColimits (f : X ⟶ S) :
    Limits.PreservesFiniteColimits (relativeRestrictionFunctor f) := sorry

/-- Derived restriction of `𝒪_X`-modules to modules over `f⁻¹𝒪_S`. -/
noncomputable def relativeRestriction (f : X ⟶ S) :
    ModuleDerived X ⥤ ModuleDerived (RingedSpace.Hom.inverseImageBase f) :=
  (relativeRestrictionFunctor f).mapDerivedCategory

/-- The canonical factorization identifying derived restriction with termwise restriction on
cochain complexes. -/
noncomputable abbrev relativeRestrictionFactors (f : X ⟶ S) :
    DerivedCategory.Q ⋙ relativeRestriction f ≅
      (relativeRestrictionFunctor f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (relativeRestrictionFunctor f).mapDerivedCategoryFactors

/-- The factorization of derived restriction is natural in a morphism of cochain complexes. -/
theorem relativeRestrictionFactors_naturality
    (f : X ⟶ S) {K L : CochainComplex X.Modules ℤ} (g : K ⟶ L) :
    (relativeRestriction f).map (DerivedCategory.Q.map g) ≫
        (relativeRestrictionFactors f).hom.app L =
      (relativeRestrictionFactors f).hom.app K ≫
        DerivedCategory.Q.map
          (((relativeRestrictionFunctor f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map g) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
