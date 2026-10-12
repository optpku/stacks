/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_31_3_EtaleSupport
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.LocallyAlgebraic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.HigherDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] {X Y : SchemeOverField K}
variable [Algebraic X] [Algebraic Y] (f : X ⟶ Y) [IsAffineHom f.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]

/-- Lemma 59.95.8: if `f : X ⟶ Y` is an affine morphism of schemes of finite type
over a field `K`, `E_a(X)` is `{x | SchemeOverField.baseFieldTrdegAt X x ≤ a}`,
and `F` is an abelian torsion sheaf on `X.left` étale with
`abelianSheafSupport F ⊆ E_a(X)`, then
`abelianSheafSupport (higherDirectImage (smallEtalePullback f.left) F q)` is
contained in `E_{a-q}(Y)`. The Lean reading of the possibly negative index
`a - q` is the inequality `SchemeOverField.baseFieldTrdegAt Y y + q ≤ a`
(so the support is empty whenever `q > a`). -/
@[stacks 0F0X]
theorem higherDirectImage_support_subset_trdeg_sub
    {a q : ℕ} (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F)
    (hsupp : abelianSheafSupport F ⊆
      {x | SchemeOverField.baseFieldTrdegAt X x ≤ a}) :
    abelianSheafSupport
        (higherDirectImage (smallEtalePullback f.left) F q :
          Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u}) ⊆
      {y | SchemeOverField.baseFieldTrdegAt Y y + q ≤ a} := sorry

/-- Geometric stalks of `higherDirectImage (smallEtalePullback f.left) F q` vanish
at geometric points `ybar` of `Y.left` with
`a < SchemeOverField.baseFieldTrdegAt Y ybar.image + q`. -/
theorem higherDirectImage_geometricStalk_isZero_of_trdeg_add_gt
    {a q : ℕ} (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F)
    (hsupp : abelianSheafSupport F ⊆
      {x | SchemeOverField.baseFieldTrdegAt X x ≤ a})
    (ybar : GeometricPoint Y.left)
    (hy : a < SchemeOverField.baseFieldTrdegAt Y ybar.image + q) :
    IsZero (geometricStalk (higherDirectImage (smallEtalePullback f.left) F q) ybar) := sorry

end AlgebraicGeometry.Scheme

end
