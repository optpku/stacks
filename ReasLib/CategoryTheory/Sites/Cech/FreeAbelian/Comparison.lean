/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.LargeColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Over
public import ReasLib.CategoryTheory.Sites.Cech.Basic
public import ReasLib.CategoryTheory.Sites.Cech.FreeAbelian
public import ReasLib.CategoryTheory.Functor.FreeAbelianYoneda.ULift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-target free-abelian Cech comparison

This leaf owns the Cech comparison for a family `family : ι → Over U`.  The simplicial object is
formed in `Over U` and is then sent to `C` by `FormalCoproduct.forgetOver U`; thus the carrier is
the presheaf complex built from genuine fibre products over `U`, without a global finite-product
assumption on `C`.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open AlgebraicTopology

noncomputable section

universe w u v

namespace CategoryTheory.Cech.FreeAbelian

variable {C : Type u} [Category.{v} C] {U : C} {ι : Type w}

/-- The degree-`n` index of a fixed-target Cech family. -/
abbrev index (family : ι → Over U) (n : ℕ) [HasIteratedFiberProducts family] :=
  (familyCech family).obj (op (SimplexCategory.mk n)) |>.I

/-- The underlying object of a degree-`n` fixed-target Cech intersection. -/
abbrev intersection (family : ι → Over U) [HasIteratedFiberProducts family]
    (n : ℕ) (i : index family n) : C :=
  ((familyCech family).obj (op (SimplexCategory.mk n))).obj i |>.left

/-- The free-abelian Cech cover chain complex attached to a fixed-target family.  The `forgetOver`
step records fibre products over `U` in presheaves on `C`. -/
@[stacks 03AS "fixed-target free-abelian Cech cover complex"]
abbrev coverComplex (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})] :
    ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ℕ :=
  (alternatingFaceMapComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})).obj
    (familyCech family ⋙ FormalCoproduct.forgetOver U ⋙
      (FormalCoproduct.eval.{w} C (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})).obj
        (FreeAbelianYoneda.ULift.functor.{u, v, u}))

/-- The coefficient presheaf functor for the fixed-target Cech nerve. -/
abbrev cochainFunctor (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasProducts AddCommGrpCat.{max u v}] :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ CochainComplex AddCommGrpCat.{max u v} ℕ :=
  restrictPresheafToOver U ⋙
    FormalCoproduct.cochainComplexFunctor (A := AddCommGrpCat.{max u v}) (familyCech family)

/-- The cochain functor represented by the free-abelian Cech cover complex. -/
@[stacks 03AS "fixed-target represented Hom cochain functor"]
abbrev homFunctor (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})] :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ CochainComplex AddCommGrpCat.{max u v} ℕ :=
  (((preadditiveCoyoneda.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (coverComplex family).op).asFunctor)

/-- The free-abelian representable summand at one fixed-target intersection. -/
abbrev summand (family : ι → Over U) [HasIteratedFiberProducts family]
    (n : ℕ) (i : index family n) : Cᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  FreeAbelianYoneda.ULift.obj.{u, v, u} (intersection family n i)

/-- The component of the Hom-to-Cech comparison on one fixed-target intersection. -/
def degreeComparisonComponentToFun (family : ι → Over U)
    [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) (i : index family n) :
    ((coverComplex family).X n ⟶ F) → F.obj (op (intersection family n i)) :=
  fun α ↦
    (Sigma.ι (fun i : index family n ↦ summand family n i) i ≫ α).app
      (op (intersection family n i))
      (FreeAbelianGroup.of (ULift.up (𝟙 (intersection family n i))))

/-- Zero preservation for the fixed-target comparison component. -/
theorem degreeComparisonComponentToFun_map_zero (family : ι → Over U)
    [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) (i : index family n) :
    degreeComparisonComponentToFun family F n i 0 = 0 := sorry

/-- Additivity of the fixed-target comparison component. -/
theorem degreeComparisonComponentToFun_map_add (family : ι → Over U)
    [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) (i : index family n)
    (α β : (coverComplex family).X n ⟶ F) :
    degreeComparisonComponentToFun family F n i (α + β) =
      degreeComparisonComponentToFun family F n i α + degreeComparisonComponentToFun family F n i β := sorry

/-- The additive comparison map at one fixed-target intersection. -/
def degreeComparisonComponent (family : ι → Over U)
    [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) (i : index family n) :
    AddCommGrpCat.of ((coverComplex family).X n ⟶ F) ⟶
      F.obj (op (intersection family n i)) :=
  AddCommGrpCat.ofHom
    { toFun := degreeComparisonComponentToFun family F n i
      map_zero' := degreeComparisonComponentToFun_map_zero family F n i
      map_add' := degreeComparisonComponentToFun_map_add family F n i }

/-- The degreewise Hom-to-Cech comparison. -/
@[stacks 03AS "fixed-target degreewise Hom-to-Cech comparison"]
def degreeComparison (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    [Limits.HasProducts AddCommGrpCat.{max u v}]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    ((homFunctor family).obj F).X n ⟶ ((cochainFunctor family).obj F).X n :=
  Pi.lift (fun i : index family n ↦ degreeComparisonComponent family F n i)

/-- Differential compatibility of the degreewise fixed-target comparison. -/
theorem degreeComparison_comm (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    [Limits.HasProducts AddCommGrpCat.{max u v}]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    ∀ i j, (ComplexShape.up ℕ).Rel i j →
      degreeComparison family F i ≫ ((cochainFunctor family).obj F).d i j =
        ((homFunctor family).obj F).d i j ≫ degreeComparison family F j := sorry

/-- The fixed-target degreewise comparison is invertible. -/
@[stacks 03AS "fixed-target degreewise comparison is invertible"]
instance degreeComparison_isIso (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    [Limits.HasProducts AddCommGrpCat.{max u v}]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    IsIso (degreeComparison family F n) := sorry

/-- The fixed-target comparison as a morphism of cochain complexes. -/
def comparisonApp (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    [Limits.HasProducts AddCommGrpCat.{max u v}]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    (homFunctor family).obj F ⟶ (cochainFunctor family).obj F :=
  HomologicalComplex.Hom.mk (fun n ↦ degreeComparison family F n) (degreeComparison_comm family F)

/-- Naturality of the fixed-target comparison in the coefficient presheaf. -/
theorem comparisonApp_natural (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    [Limits.HasProducts AddCommGrpCat.{max u v}]
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (φ : F ⟶ G) :
    (homFunctor family).map φ ≫ comparisonApp family G =
      comparisonApp family F ≫ (cochainFunctor family).map φ := sorry

/-- The natural fixed-target Hom-to-Cech comparison. -/
@[stacks 03AS "fixed-target natural Hom-to-Cech comparison"]
def comparison (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    [Limits.HasProducts AddCommGrpCat.{max u v}] :
    homFunctor family ⟶ cochainFunctor family where
  app := comparisonApp family
  naturality := fun _ _ φ ↦ comparisonApp_natural family φ

/-- The natural fixed-target comparison is invertible. -/
@[stacks 03AS "fixed-target natural comparison is invertible"]
instance comparison_isIso (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    [Limits.HasProducts AddCommGrpCat.{max u v}] : IsIso (comparison family) := sorry

/-- The fixed-target comparison at a coefficient presheaf is invertible. -/
instance comparisonApp_isIso (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    [Limits.HasProducts AddCommGrpCat.{max u v}]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) : IsIso (comparisonApp family F) := sorry

/-- The fixed-target Hom-to-Cech comparison isomorphism at a coefficient presheaf. -/
noncomputable def comparisonAppIso (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    [Limits.HasProducts AddCommGrpCat.{max u v}]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    (homFunctor family).obj F ≅ (cochainFunctor family).obj F :=
  asIso (comparisonApp family F)

/-- The fixed-target free-abelian Cech cover complex is exact in positive degrees. -/
@[stacks 03AT "fixed-target free-abelian Cech homology vanishing"]
theorem coverComplex_homology_isZero_succ (family : ι → Over U)
    [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    (i : ℕ) :
    IsZero ((coverComplex family).homology (i + 1)) := sorry

/-- Positive-degree form of the fixed-target Cech homology vanishing theorem. -/
theorem coverComplex_homology_isZero_of_pos (family : ι → Over U)
    [HasIteratedFiberProducts family]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    (i : ℕ) (hi : 0 < i) :
    IsZero ((coverComplex family).homology i) := sorry

end CategoryTheory.Cech.FreeAbelian
