/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.LCCat.SmallToSlice.Derived
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Hypercohomology
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomology on the canonical small and qc sites

This leaf owns the concrete source-facing cohomology comparisons for `LCCat`.  It keeps the
raised-universe objectwise cohomology owner and the all-integer bounded-derived sections owner
explicit, so downstream files can import the statements without importing a chapter.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open TopologicalSpace
open scoped CategoryTheory CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace LCCat.SmallToSlice

section Cohomology

variable (X : LCCat.{u})
variable [HasWeakSheafify (LCCat.zarTopology.over X) AddCommGrpCat.{u + 1}]
variable [HasSheafify
  (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})]
variable [HasSheafify (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1}
  (Sheaf (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1})]

/- The qc-side view is named separately so callers do not have to repeat the raised-universe
   `cohomologyOverObject` application in every comparison statement. -/
/-- The objectwise qc cohomology of a sheaf on the canonical qc slice site. -/
@[stacks 09X4 "qc cohomology view"]
noncomputable abbrev qcCohomology
    (F : Sheaf (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    AddCommGrpCat.{u + 1} :=
  @CategoryTheory.Sheaf.cohomologyOverObject.{u + 1, u + 1, u, u + 1}
    (Over X) _ (LCCat.qcTopology.over X) F inferInstance inferInstance
    (Over.mk (𝟙 X)) n

/-- Lemma 21.31.12 (1): ordinary cohomology of a small-site abelian sheaf agrees with the
cohomology of its canonical inverse image on the qc slice site. -/
@[stacks 09X4 "(1)"]
theorem cohomology_isomorphic_qcPullback
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})
    (n : ℕ) :
    IsIsomorphic
      (smallCohomology X F (⊤ : Opens X.obj) n)
      (qcCohomology X
        ((aInverseAb X).obj F) n) := sorry

end Cohomology

section Hypercohomology

variable (X : LCCat.{u})
variable [HasSheafify
  (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
variable [HasSheafify (LCCat.zarTopology.over X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1}]
variable [Functor.HasRightDerivedFunctor
  ((siteAbelianSectionsFunctor.{u, u, u + 1}
    (Opens.grothendieckTopology X.obj)
    (⊤ : Opens X.obj)).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}))]
variable [Functor.HasRightDerivedFunctor
  ((siteAbelianSectionsFunctor.{u + 1, u, u + 1}
    (LCCat.qcTopology.over X)
    (Over.mk (𝟙 X))).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1}))]

/-- The small-site bounded-below hypercohomology in an integer degree. -/
@[stacks 09X4 "small hypercohomology view"]
noncomputable abbrev smallHypercohomology
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})) (n : ℤ) :
    AddCommGrpCat.{u + 1} :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} n).obj
    ((siteAbelianSectionsBoundedBelowDerived.{u, u, u + 1}
      (Opens.grothendieckTopology X.obj) (⊤ : Opens X.obj)).obj K)

/-- The qc-side bounded-below hypercohomology after the canonical inverse image. -/
@[stacks 09X4 "qc hypercohomology view"]
noncomputable abbrev qcHypercohomology
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})) (n : ℤ) :
    AddCommGrpCat.{u + 1} :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} n).obj
    ((siteAbelianSectionsBoundedBelowDerived.{u + 1, u, u + 1}
      (LCCat.qcTopology.over X) (Over.mk (𝟙 X))).obj
        ((aInverseAbPlus X).obj K))

/-- Lemma 21.31.12 (2): bounded-below hypercohomology agrees in every integer degree after the
canonical inverse image from the small site to the qc slice site. -/
@[stacks 09X4 "(2)"]
theorem hypercohomology_isomorphic_qcPullback
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    IsIsomorphic
      (smallHypercohomology X K n) (qcHypercohomology X K n) := sorry

end Hypercohomology

section Constant

variable (X : LCCat.{u})
variable [HasWeakSheafify (LCCat.zarTopology.over X) AddCommGrpCat.{u + 1}]
variable [HasSheafify
  (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
variable [HasSheafify (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 1}
  (Sheaf (LCCat.qcTopology.over X) AddCommGrpCat.{u + 1})]

/-- Lemma 21.31.12, constant-sheaf example: the small and qc cohomology of a constant abelian
group are compared after applying the canonical inverse image, rather than by naming an
independent qc constant sheaf. -/
@[stacks 09X4 "constant sheaf example"]
theorem constantCohomology_isomorphic_qc
    (A : AddCommGrpCat.{u + 1}) (n : ℕ) :
    IsIsomorphic
      (smallCohomology X
        ((constantSheaf (Opens.grothendieckTopology X.obj)
          AddCommGrpCat.{u + 1}).obj A)
        (⊤ : Opens X.obj) n)
      (qcCohomology X
        ((aInverseAb X).obj
          ((constantSheaf (Opens.grothendieckTopology X.obj)
            AddCommGrpCat.{u + 1}).obj A)) n) := sorry

/-- Lemma 21.31.12, constant-sheaf source view: the qc-side constant sheaf is the concrete
presentation used in the textbook example.  The canonical-pullback theorem above is the
preferred reusable root; this companion preserves the source-facing presentation. -/
@[stacks 09X4 "constant sheaf source view"]
theorem constantCohomology_isomorphic_qcConstant
    (A : AddCommGrpCat.{u + 1}) (n : ℕ) :
    IsIsomorphic
      (smallCohomology X
        ((constantSheaf (Opens.grothendieckTopology X.obj)
          AddCommGrpCat.{u + 1}).obj A)
        (⊤ : Opens X.obj) n)
      (qcCohomology X
        ((constantSheaf (LCCat.qcTopology.over X)
          AddCommGrpCat.{u + 1}).obj A) n) := sorry

end Constant

end LCCat.SmallToSlice

end
