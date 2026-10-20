/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FiniteLength
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import ReasLib.CategoryTheory.InverseSystem.Sequential.PrincipalTorsion.Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stage-one images in principal torsion cohomology towers

The image and intersection objects used in the finite-length refinement are independent of a
particular textbook proof.  They are exposed here as submodules so later arguments can use the
same objects without rebuilding linear transition maps.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SequentialInverseSystem.PrincipalTorsion.Cohomology

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

/-- The image in stage `1` of the degree-`p` cohomology transition from stage `n + 1`. -/
@[stacks 0DXG "stage-one cohomology image"]
abbrev stageOneImage
    (F : SequentialInverseSystem (Sheaf J (ModuleCat A))) (p n : ℕ) :
    Submodule A ((siteModuleCohomologyFunctor p).obj (F.obj (op 1))) :=
  LinearMap.range (siteModuleCohomologyTransitionMapLinear F p
    (Nat.succ_le_succ (Nat.zero_le n)))

/-- The intersection of all stage-one images in a fixed degree. -/
@[stacks 0DXG "intersection of stage-one cohomology images"]
def stageOneImageInf
    (F : SequentialInverseSystem (Sheaf J (ModuleCat A))) (p : ℕ) :
    Submodule A ((siteModuleCohomologyFunctor p).obj (F.obj (op 1))) :=
  ⨅ n : ℕ, stageOneImage F p n

/-- The canonical inclusion of the all-stage intersection into any stage-one image. -/
@[stacks 0DXG "intersection inclusion into a stage-one image"]
theorem stageOneImageInf_le
    (F : SequentialInverseSystem (Sheaf J (ModuleCat A))) (p n : ℕ) :
    stageOneImageInf F p ≤ stageOneImage F p n := sorry

/-- A finite-length stage-one image gives finite length to the common intersection. -/
@[stacks 0DXG "finite-length intersection of stage-one images"]
theorem stageOneImageInf_isFiniteLength_of
    (F : SequentialInverseSystem (Sheaf J (ModuleCat A))) (p n : ℕ)
    (hfinite : IsFiniteLength A (stageOneImage F p n)) :
    IsFiniteLength A (stageOneImageInf F p) := sorry

/-- Lemma 20.36.5 (0DXG): under a principal torsion presentation, finite-length control of one
stage-one image, or Noetherian finite control of their intersection, makes the positive cohomology
tail Mittag–Leffler. -/
@[stacks 0DXG "Mittag-Leffler tail from stage-one images"]
theorem isMittagLeffler_of_stageOneImageFinite
    (f : A) (F : SequentialInverseSystem (Sheaf J (ModuleCat A))) (p : ℕ)
    (hF : PrincipalTorsion.IsPresented f F)
    (hfinite :
      (∃ n : ℕ, IsFiniteLength A (stageOneImage F (p + 1) n)) ∨
      (IsNoetherianRing A ∧ Module.Finite A (stageOneImageInf F (p + 1)))) :
    ((siteModuleCohomologyModuleTower F p).shift 1).IsMittagLeffler := sorry

end CategoryTheory.SequentialInverseSystem.PrincipalTorsion.Cohomology
