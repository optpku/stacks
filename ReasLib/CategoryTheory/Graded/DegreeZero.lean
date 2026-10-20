/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Graded
public import ReasLib.CategoryTheory.Preadditive.InducedWideCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-zero categories

This leaf packages the degree-zero part of a graded category through mathlib's
`WideSubcategory`, retaining the ambient objects and only degree-zero morphisms.
-/

@[expose] public section

namespace CategoryTheory

universe x w v u

namespace GradedCategory

section

open Limits
variable {ι : Type x} [DecidableEq ι] [AddMonoid ι]
variable {R : Type w} [Semiring R] {C : Type u} [Category.{v} C] [Preadditive C]
variable [GradedCategory R C ι]

/-- The morphism property selecting the degree-zero component of each hom module. -/
def degreeZeroMorphismProperty : MorphismProperty C :=
  fun X Y f ↦ f ∈ GradedCategory.homDegree (R := R) (ι := ι) X Y 0

/-- A morphism belongs to `degreeZeroMorphismProperty` exactly when it has degree zero. -/
@[simp]
theorem degreeZeroMorphismProperty_iff {X Y : C} {f : X ⟶ Y} :
    degreeZeroMorphismProperty (R := R) (ι := ι) f ↔
      f ∈ GradedCategory.homDegree (R := R) (ι := ι) X Y 0 := sorry

namespace degreeZeroMorphismProperty

/-- Degree-zero morphisms are closed under identities and composition. -/
instance isMultiplicative :
    MorphismProperty.IsMultiplicative
      (degreeZeroMorphismProperty (R := R) (ι := ι) : MorphismProperty C) := sorry

end degreeZeroMorphismProperty

/-- The category with the same objects as `C` and only degree-zero morphisms.

This is the canonical categorical realization of the degree-zero category of a graded category. -/
@[stacks 09ML]
abbrev DegreeZero (C : Type u) [Category.{v} C] [Preadditive C]
    (ι : Type x) [DecidableEq ι] [AddMonoid ι] [GradedCategory R C ι] : Type u :=
  WideSubcategory (degreeZeroMorphismProperty (R := R) (ι := ι) : MorphismProperty C)

namespace DegreeZero

/-- A morphism in the degree-zero category belongs to the degree-zero hom submodule. -/
@[simp]
theorem hom_mem_homDegree_zero {X Y : DegreeZero (R := R) C ι} (f : X ⟶ Y) :
    f.hom ∈ GradedCategory.homDegree (R := R) (ι := ι) X.obj Y.obj 0 := sorry

/-- The degree-zero category inherits zero morphisms from the degree-zero submodules. -/
instance instHasZeroMorphisms : Limits.HasZeroMorphisms (DegreeZero (R := R) C ι) where
  zero X Y :=
    ⟨(0 : X.obj ⟶ Y.obj), Submodule.zero_mem _⟩
  comp_zero := sorry
  zero_comp := sorry

/-- Forgetting a zero morphism in the degree-zero category gives the ambient zero morphism. -/
@[simp]
theorem zero_hom {X Y : DegreeZero (R := R) C ι} :
    (0 : X ⟶ Y).hom = (0 : X.obj ⟶ Y.obj) := sorry

end DegreeZero

end

section

variable {ι : Type x} [DecidableEq ι] [AddMonoid ι]
variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C]
variable [GradedCategory R C ι]

namespace degreeZeroMorphismProperty

/-- Degree-zero morphisms are closed under the additive operations of the ambient category. -/
instance isPreadditive :
    MorphismProperty.IsPreadditive
      (degreeZeroMorphismProperty (R := R) (ι := ι) : MorphismProperty C) := sorry

end degreeZeroMorphismProperty

namespace DegreeZero

variable {X Y : DegreeZero (R := R) C ι}

/-- Scalar multiplication of degree-zero morphisms is inherited from the ambient hom module. -/
instance instSMulHom : SMul R (X ⟶ Y) where
  smul r f := ⟨r • f.hom, sorry⟩

/-- The underlying ambient morphism of a scalar multiple is the corresponding scalar multiple. -/
@[simp]
theorem smul_hom (r : R) (f : X ⟶ Y) : (r • f).hom = r • f.hom := sorry

/-- Every degree-zero hom group inherits the ambient `R`-module structure. -/
instance instModuleHom : Module R (X ⟶ Y) :=
  Function.Injective.module R
    { toFun := InducedWideCategory.Hom.hom
      map_zero' := sorry
      map_add' := sorry }
    sorry (fun _ _ ↦ sorry)

/-- The degree-zero category inherits its `R`-linear structure from the ambient category. -/
instance instLinear : Linear R (DegreeZero (R := R) C ι) where
  homModule := fun X Y ↦ instModuleHom (X := X) (Y := Y)
  smul_comp := sorry
  comp_smul := sorry

/-- The inclusion of the degree-zero category into the ambient category is `R`-linear. -/
instance inclusionLinear :
    Functor.Linear R
      (wideSubcategoryInclusion
        (degreeZeroMorphismProperty (R := R) (C := C) (ι := ι))) := sorry

end DegreeZero

end

end GradedCategory

end CategoryTheory
