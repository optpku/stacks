module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianSupport
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.LocallyAlgebraic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.HigherDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- For an affine morphism of schemes of finite type over a field, the degree-`q` higher
direct image of a locally torsion abelian étale sheaf supported at points of transcendence
degree at most `a` is supported where the transcendence degree plus `q` is at most `a`.
In particular, its support is empty when `q > a`. -/
theorem higherDirectImage_support_subset_trdeg_sub
    {K : Type u} [Field K] {X Y : SchemeOverField K}
    [Algebraic X] [Algebraic Y] (f : X ⟶ Y) [IsAffineHom f.left]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    {a q : ℕ} (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F)
    (hsupp : abelianSheafSupport F ⊆
      {x | SchemeOverField.baseFieldTrdegAt X x ≤ a}) :
    abelianSheafSupport
        (higherDirectImage (smallEtalePullback f.left) F q :
          Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u}) ⊆
      {y | SchemeOverField.baseFieldTrdegAt Y y + q ≤ a} := sorry

/-- For an affine morphism of schemes of finite type over a field, the degree-`q` higher
direct image of a locally torsion abelian étale sheaf supported at points of transcendence
degree at most `a` has zero geometric stalk wherever the transcendence degree plus `q`
is greater than `a`. -/
theorem higherDirectImage_geometricStalk_isZero_of_trdeg_add_gt
    {K : Type u} [Field K] {X Y : SchemeOverField K}
    [Algebraic X] [Algebraic Y] (f : X ⟶ Y) [IsAffineHom f.left]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    {a q : ℕ} (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F)
    (hsupp : abelianSheafSupport F ⊆
      {x | SchemeOverField.baseFieldTrdegAt X x ≤ a})
    (ybar : GeometricPoint Y.left)
    (hy : a < SchemeOverField.baseFieldTrdegAt Y ybar.image + q) :
    IsZero (geometricStalk (higherDirectImage (smallEtalePullback f.left) F q) ybar) := sorry

end AlgebraicGeometry.Scheme

end
