/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import ReasLib.Topology.Opens.Instances

/-!
# Čech complexes of presheaves on topological spaces

This module specializes Mathlib's Čech-complex functor to a family of opens of a topological
space.  The finite-product structure on opens is supplied by
`ReasLib.Topology.Opens.Instances`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u uι

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {ι : Type uι}

/-- The Čech complex of an abelian presheaf for an indexed family of opens. -/
@[stacks 01EF]
abbrev cechComplex (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u uι}) :
    CochainComplex AddCommGrpCat.{max u uι} ℕ :=
  (cechComplexFunctor U).obj F

/-- The degree-`i` Čech cohomology group of a presheaf for an indexed family of opens. -/
abbrev cechCohomology (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u uι}) (i : ℕ) :
    AddCommGrpCat.{max u uι} :=
  (cechComplex U F).homology i

/-- Čech cohomology is the degree-`i` homology object of the associated Čech complex. -/
@[simp] theorem cechComplex_homology
    (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u uι}) (i : ℕ) :
    (cechComplex U F).homology i = cechCohomology U F i := sorry

/-- The Čech-complex functor on abelian presheaves for an indexed family of opens. -/
abbrev cechComplexOnPresheaves (U : ι → Opens X) :
    X.Presheaf AddCommGrpCat.{max u uι} ⥤ CochainComplex AddCommGrpCat.{max u uι} ℕ :=
  cechComplexFunctor U

/-- Evaluating the Čech-complex functor gives the Čech complex of the presheaf. -/
@[simp] theorem cechComplexOnPresheaves_obj
    (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u uι}) :
    (cechComplexOnPresheaves U).obj F = cechComplex U F := sorry

/-- The morphism part of the topological Čech-complex functor is the morphism induced by
`cechComplexFunctor U`. -/
@[simp] theorem cechComplexOnPresheaves_map
    (U : ι → Opens X) {F G : X.Presheaf AddCommGrpCat.{max u uι}} (α : F ⟶ G) :
    (cechComplexOnPresheaves U).map α = (cechComplexFunctor U).map α := sorry

end TopCat.Presheaf
