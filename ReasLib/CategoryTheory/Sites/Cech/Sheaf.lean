/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Sites.Cech.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Čech cohomology on abelian sheaves

This leaf owns the sheaf-level view of the additive Čech cohomology construction.  The
construction is defined directly from the reusable slice Čech complex, so later developments do
not need to import a numbered chapter merely to obtain its degreewise functor or its standard
acyclicity consequences.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U : C} {ι : Type w}
variable [Limits.HasFiniteProducts (Over U)]
variable [HasProducts AddCommGrpCat.{v}]

/-- The degree-`p` Čech cohomology functor of a covering family, restricted from abelian
presheaves to abelian sheaves. -/
@[stacks 03AW "Čech cohomology functor on abelian sheaves"]
noncomputable def cechCohomologyOnSheaves
    (J : GrothendieckTopology C) (family : ι → Over U) (p : ℕ) :
    Sheaf J AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v} :=
  sheafToPresheaf J AddCommGrpCat.{v} ⋙
    (cechComplexOnPresheaves U family ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p)

/-- Evaluating `cechCohomologyOnSheaves J family p` recovers the degree-`p` Čech cohomology
object of the underlying abelian presheaf. -/
@[simp]
theorem cechCohomologyOnSheaves_obj_obj
    (family : ι → Over U) (p : ℕ) (F : Sheaf J AddCommGrpCat.{v}) :
    (cechCohomologyOnSheaves J family p).obj F =
      cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{v}).obj F) p :=
  sorry

/-- For a covering family of `U`, degree-zero Čech cohomology of an abelian sheaf is isomorphic
to its sections over `U`. -/
@[stacks 03AW "degree-zero Čech cohomology of a sheaf"]
theorem cechCohomology_zero_of_sheaf
    (J : GrothendieckTopology C) (family : ι → Over U)
    (hfamily : (J.over U).CoversTop family)
    (F : Sheaf J AddCommGrpCat.{v}) :
    IsIsomorphic
      (cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{v}).obj F) 0)
      (((sheafSections J AddCommGrpCat.{v}).obj (op U)).obj F) :=
  sorry

/-- The sheaf-level form of the degree-zero Čech/sections comparison. -/
theorem cechCohomologyOnSheaves_zero_of_sheaf
    (J : GrothendieckTopology C) (family : ι → Over U)
    (hfamily : (J.over U).CoversTop family)
    (F : Sheaf J AddCommGrpCat.{v}) :
    IsIsomorphic ((cechCohomologyOnSheaves J family 0).obj F)
      (((sheafSections J AddCommGrpCat.{v}).obj (op U)).obj F) :=
  sorry

/-- Positive successor degrees of Čech cohomology vanish on an injective abelian sheaf. -/
@[stacks 03AW "positive Čech acyclicity of injective sheaves"]
theorem cechCohomology_isZero_of_injective_succ
    (J : GrothendieckTopology C) (family : ι → Over U)
    (F : Sheaf J AddCommGrpCat.{v}) [Injective F] (p : ℕ) :
    IsZero (cechCohomology U family
      ((sheafToPresheaf J AddCommGrpCat.{v}).obj F) (p + 1)) :=
  sorry

/-- The sheaf-level form of positive-degree Čech acyclicity for an injective coefficient. -/
theorem cechCohomologyOnSheaves_isZero_of_injective_succ
    (J : GrothendieckTopology C) (family : ι → Over U)
    (F : Sheaf J AddCommGrpCat.{v}) [Injective F] (p : ℕ) :
    IsZero ((cechCohomologyOnSheaves J family (p + 1)).obj F) :=
  sorry

/-- Positive-degree form of Čech acyclicity for an injective abelian sheaf. -/
theorem cechCohomology_isZero_of_pos_of_injective
    (J : GrothendieckTopology C) (family : ι → Over U)
    (F : Sheaf J AddCommGrpCat.{v}) [Injective F] (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology U family
      ((sheafToPresheaf J AddCommGrpCat.{v}).obj F) p) :=
  sorry

/-- Sheaf-level positive-degree form of Čech acyclicity for an injective coefficient. -/
theorem cechCohomologyOnSheaves_isZero_of_pos_of_injective
    (J : GrothendieckTopology C) (family : ι → Over U)
    (F : Sheaf J AddCommGrpCat.{v}) [Injective F] (p : ℕ) (hp : 0 < p) :
    IsZero ((cechCohomologyOnSheaves J family p).obj F) :=
  sorry

end CategoryTheory
