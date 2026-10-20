module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage.Support
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

universe u

/- Lemma 59.95.8: the higher direct image support bound for an affine morphism
of schemes of finite type over a field. -/
@[stacks 0F0X] #check (AlgebraicGeometry.Scheme.higherDirectImage_support_subset_trdeg_sub :
  ∀ {K : Type u} [Field K] {X Y : SchemeOverField K}
    [Algebraic X] [Algebraic Y] (f : X ⟶ Y) [IsAffineHom f.left]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    {a q : ℕ} (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F)
    (hsupp : abelianSheafSupport F ⊆
      {x | SchemeOverField.baseFieldTrdegAt X x ≤ a}),
    abelianSheafSupport
        (higherDirectImage (smallEtalePullback f.left) F q :
          Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u}) ⊆
      {y | SchemeOverField.baseFieldTrdegAt Y y + q ≤ a})

#check (AlgebraicGeometry.Scheme.higherDirectImage_geometricStalk_isZero_of_trdeg_add_gt :
  ∀ {K : Type u} [Field K] {X Y : SchemeOverField K}
    [Algebraic X] [Algebraic Y] (f : X ⟶ Y) [IsAffineHom f.left]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    {a q : ℕ} (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F)
    (hsupp : abelianSheafSupport F ⊆
      {x | SchemeOverField.baseFieldTrdegAt X x ≤ a})
    (ybar : GeometricPoint Y.left)
    (hy : a < SchemeOverField.baseFieldTrdegAt Y ybar.image + q),
    IsZero (geometricStalk (higherDirectImage (smallEtalePullback f.left) F q) ybar))
