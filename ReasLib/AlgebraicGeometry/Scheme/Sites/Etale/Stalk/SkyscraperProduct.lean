/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Coproduct

/-!
# Fibrewise products of abelian étale skyscraper sheaves

Products of skyscraper sheaves over same-field geometric lifts are right
adjoint to the corresponding coproducts of stalks.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y)
variable [HasProducts.{u} AddCommGrpCat.{u}]

/-- The fibrewise product of abelian skyscraper sheaves at geometric points of
`X` over `ybar`. -/
def abelianSkyscraperProduct :
    AddCommGrpCat.{u} ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u} where
  obj A := ∏ᶜ fun x : Fiber f ybar ↦
    (toSmallEtalePoint x.point).skyscraperSheafFunctor.obj A
  map {A B} φ := Limits.Pi.map fun x : Fiber f ybar ↦
    (toSmallEtalePoint x.point).skyscraperSheafFunctor.map φ
  map_id := sorry
  map_comp := sorry

/-- Evaluating the fibrewise abelian skyscraper product recovers the product of
skyscrapers. -/
theorem abelianSkyscraperProduct_obj (A : AddCommGrpCat.{u}) :
    (abelianSkyscraperProduct f ybar).obj A =
      ∏ᶜ fun x : Fiber f ybar ↦
        (toSmallEtalePoint x.point).skyscraperSheafFunctor.obj A :=
  sorry

/-- The skyscraper-product functor acts on a morphism of abelian groups by the
product of the induced skyscraper maps. -/
theorem abelianSkyscraperProduct_map {A B : AddCommGrpCat.{u}} (φ : A ⟶ B) :
    (abelianSkyscraperProduct f ybar).map φ =
      Limits.Pi.map fun x : Fiber f ybar ↦
        (toSmallEtalePoint x.point).skyscraperSheafFunctor.map φ :=
  sorry

/-- The fibrewise coproduct of abelian stalks is left adjoint to the fibrewise
product of skyscrapers, via the product/coproduct and skyscraper
hom-equivalences. -/
def abelianStalkCoproductAdjunction :
    abelianStalkCoproduct f ybar ⊣ abelianSkyscraperProduct f ybar :=
  Adjunction.mkOfHomEquiv
    { homEquiv F A :=
        { toFun g :=
            Pi.lift fun x : Fiber f ybar ↦
              ((toSmallEtalePoint x.point).skyscraperSheafAdjunction.homEquiv
                  F A)
                (Sigma.ι (fun y : Fiber f ybar ↦
                    (toSmallEtalePoint y.point).sheafFiber.obj F) x ≫ g)
          invFun h :=
            Sigma.desc fun x : Fiber f ybar ↦
              ((toSmallEtalePoint x.point).skyscraperSheafAdjunction.homEquiv
                  F A).symm
                (h ≫ Pi.π (fun y : Fiber f ybar ↦
                    (toSmallEtalePoint y.point).skyscraperSheafFunctor.obj A) x)
          left_inv := sorry
          right_inv := sorry }
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The hom-equivalence of `abelianStalkCoproductAdjunction`. -/
def abelianStalkCoproductAdjunction_homEquiv
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (A : AddCommGrpCat.{u}) :
    ((abelianStalkCoproduct f ybar).obj F ⟶ A) ≃
      (F ⟶ (abelianSkyscraperProduct f ybar).obj A) :=
  (abelianStalkCoproductAdjunction f ybar).homEquiv F A


end AlgebraicGeometry.Scheme.Etale

end
