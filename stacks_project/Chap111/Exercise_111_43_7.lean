/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Exercise_111_54_4_AffineTriangle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Cohomology
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exercise 111.43.7

The affine triangle is an affine scheme with nontrivial Picard group, so
Zariski `H¹(X, -)` on abelian sheaves is not the zero functor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry.AffineTriangle

/-- Exercise 111.43.7 (1): the affine scheme `scheme k`, namely
`Spec` of `k[x, y] ⧸ (x * y * (x + y + 1))`, has nontrivial Picard group
whenever `kˣ` is nontrivial. -/
@[stacks 0DAQ, instance]
instance nontrivial_picardGroup (k : Type u) [Field k] [Nontrivial kˣ] :
    Nontrivial (scheme k).PicardGroup := sorry

end AlgebraicGeometry.AffineTriangle

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.toRingedSpace) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toRingedSpace) AddCommGrpCat.{u})]

/-- Exercise 111.43.7 (2): for a scheme `X` with nontrivial Picard group, the
Zariski abelian-sheaf functor `Sheaf.functorH` in degree 1 is not the zero
functor. In particular this holds for any affine scheme with nontrivial Picard
group, such as `AffineTriangle.scheme k` when `kˣ` is nontrivial. -/
@[stacks 0DAQ]
theorem functorH_one_not_isZero [Nontrivial X.PicardGroup] :
    ¬ IsZero (Sheaf.functorH (Opens.grothendieckTopology X.toRingedSpace) 1) :=
  sorry

/-- Evaluating `Sheaf.functorH` in degree 1 at `Sheaf.unitsAddSheaf` of the
structure sheaf of `X` yields a nonzero object of `AddCommGrpCat`. -/
theorem unitsAddSheaf_functorH_one_not_isZero [Nontrivial X.PicardGroup] :
    ¬ IsZero
        ((Sheaf.functorH (Opens.grothendieckTopology X.toRingedSpace) 1).obj
          (Sheaf.unitsAddSheaf X.toRingedSpace.sheaf)) :=
  sorry

end AlgebraicGeometry.Scheme
