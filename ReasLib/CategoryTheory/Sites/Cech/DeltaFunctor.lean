/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.ExactComplex
public import ReasLib.CategoryTheory.Sites.Cech.Cohomology
public import ReasLib.CategoryTheory.Sites.Cech.Exact
public import ReasLib.CategoryTheory.Sites.Cech.FreeAbelian.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cech cohomology as a delta functor

When the required products in the Abelian coefficient category are exact, the exact Cech-complex
functor gives a cohomological delta functor by the generic
`CohomologicalDeltaFunctor.ExactComplex` construction. This module only specializes that
construction; the long exact sequence machinery remains in the generic homology layer.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.CohomologicalDeltaFunctor

noncomputable section

universe w vA uA v u

namespace CategoryTheory.Cech

variable {C : Type u} [Category.{v} C]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)
variable [HasProducts.{w} A] [AB4StarOfSize.{w} A]

/-- Cech cohomology for a family in `Over U` forms a cohomological delta functor for
presheaves valued in the Abelian category `A`. -/
@[stacks 03AR]
noncomputable def deltaFunctor :
    CohomologicalDeltaFunctor (Cᵒᵖ ⥤ A) A :=
  ExactComplex.functorBundled (complexExactFunctor U family)

/-- The connecting morphism in Cech cohomology induced by a short exact sequence of
`A`-valued presheaves. -/
@[stacks 03AR "Cech cohomology connecting morphism"]
noncomputable abbrev connecting
    {S : ShortComplex (Cᵒᵖ ⥤ A)}
    (hS : S.ShortExact) (n : ℕ) :
    ((cohomologyFunctor U family n).obj).obj S.X₃ ⟶
      ((cohomologyFunctor U family (n + 1)).obj).obj S.X₁ :=
  (deltaFunctor U family).δ hS n

/-- The degree branches of `deltaFunctor` are the canonical Cech cohomology functors. -/
@[simp]
theorem deltaFunctor_obj (n : ℕ) :
    ((deltaFunctor U family).F n).obj =
      (cohomologyFunctor (A := A) U family n).obj := sorry

/-- Evaluating a degree branch of `deltaFunctor` gives the corresponding Cech cohomology
object. -/
@[simp]
theorem deltaFunctor_obj_obj (n : ℕ) (F : Cᵒᵖ ⥤ A) :
    (((deltaFunctor U family).F n).obj).obj F = cechCohomology U family F n := sorry

/-- The connecting map of `deltaFunctor` is the boundary map of the mapped short exact
sequence. -/
@[simp]
theorem deltaFunctor_δ
    {S : ShortComplex (Cᵒᵖ ⥤ A)}
    (hS : S.ShortExact) (n : ℕ) :
    (deltaFunctor U family).δ hS n = connecting U family hS n := sorry

end CategoryTheory.Cech

namespace CategoryTheory.Cech.FixedTarget

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CohomologicalDeltaFunctor

variable {C : Type u} [Category.{v} C] {U : C} {ι : Type w}
variable (family : ι → Over U)
variable [HasIteratedFiberProducts family]
variable [HasProducts.{w} AddCommGrpCat.{max u v}]

/-- Additivity of the fixed-target Cech cochain functor in its presheaf coefficient. -/
@[stacks 03AQ "additivity of the fixed-target Cech cochain functor"]
noncomputable instance cochainFunctor_additive :
    (cochainFunctor family).Additive := sorry

/-- The degree-`n` fixed-target Cech cohomology functor. -/
@[stacks 03AR "fixed-target Cech cohomology functor"]
abbrev cohomologyFunctor (family : ι → Over U) [HasIteratedFiberProducts family] (n : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤+ AddCommGrpCat.{max u v} :=
  AdditiveFunctor.of (cochainFunctor family ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) n)

/-- The fixed-target Cech cohomology object of a presheaf. -/
abbrev cohomology (family : ι → Over U) [HasIteratedFiberProducts family]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    AddCommGrpCat.{max u v} :=
  (cochainFunctor family).obj F |>.homology n

/-- The underlying functor of fixed-target Cech cohomology is homology of the cochain functor. -/
@[simp]
theorem cohomologyFunctor_obj (family : ι → Over U) [HasIteratedFiberProducts family] (n : ℕ) :
    (cohomologyFunctor family n).obj = cochainFunctor family ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) n := sorry

/-- Evaluating fixed-target Cech cohomology at a presheaf gives its homology object. -/
@[simp]
theorem cohomologyFunctor_obj_obj (family : ι → Over U) [HasIteratedFiberProducts family]
    (n : ℕ) (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    ((cohomologyFunctor family n).obj).obj F = cohomology family F n := sorry

/-- The fixed-target cohomological delta functor obtained from the exact Cech cochain functor. -/
@[stacks 03AR "fixed-target Cech delta functor"]
noncomputable def deltaFunctor :
    CohomologicalDeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) AddCommGrpCat.{max u v} :=
  ExactComplex.functorOfExact (cochainFunctor family) (cochainFunctor_exact family)

/-- The degree branches of the fixed-target delta functor are the fixed-target cohomology
functors. -/
@[simp]
theorem deltaFunctor_obj (family : ι → Over U) [HasIteratedFiberProducts family] (n : ℕ) :
    ((deltaFunctor family).F n).obj = (cohomologyFunctor family n).obj := sorry

/-- The connecting morphism of the fixed-target Cech delta functor. -/
@[stacks 03AR "fixed-target Cech connecting morphism"]
noncomputable abbrev connecting {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})}
    (hS : S.ShortExact) (n : ℕ) :
    ((cohomologyFunctor family n).obj).obj S.X₃ ⟶
      ((cohomologyFunctor family (n + 1)).obj).obj S.X₁ :=
  (deltaFunctor family).δ hS n

end CategoryTheory.Cech.FixedTarget
