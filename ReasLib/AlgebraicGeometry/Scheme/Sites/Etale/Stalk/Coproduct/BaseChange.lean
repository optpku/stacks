/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantPullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Pullback

/-!
# Base change of coproducts of geometric stalks

The cartesian equivalence of geometric lifts reindexes the coproduct of
abelian stalks, using the inverse-image stalk identification on each summand.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)

/-- The stalk identification `F_x̄ ≅ ((g')⁻¹ F)_{x̄'}` on a summand of the fibre
coproduct, for `x̄'` the cartesian lift of `x̄`. -/
def abelianStalkCoproductBaseChangeIso_summand (ybar' : GeometricPoint Y')
    (x : Fiber f (ybar'.map g))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint
          ((Fiber.baseChangeEquiv f g f' g' h_cart ybar').symm x).point).sheafFiber.obj
        ((etaleAbelianSheafPullback g').obj F) ≅
      (toSmallEtalePoint x.point).sheafFiber.obj F :=
  (pullbackSheafFiberIso g'
        ((Fiber.baseChangeEquiv f g f' g' h_cart ybar').symm x).point F).symm ≪≫
    eqToIso
      (congrArg (fun p : GeometricPoint X ↦
          (toSmallEtalePoint p).sheafFiber.obj F)
        (Fiber.baseChangeEquiv_symm_point f g f' g' h_cart ybar' x))

/-- Reindexing `⊕_{f(x̄)=ȳ} F_x̄` along `Fiber.baseChangeEquiv` and identifying
summands by `pullbackSheafFiberIso`. -/
def abelianStalkCoproductBaseChangeIso (ybar' : GeometricPoint Y') :
    abelianStalkCoproduct f (ybar'.map g) ≅
      etaleAbelianSheafPullback g' ⋙ abelianStalkCoproduct f' ybar' :=
  NatIso.ofComponents
    (fun F ↦
      Sigma.whiskerEquiv (Fiber.baseChangeEquiv f g f' g' h_cart ybar').symm
        (fun x ↦
          abelianStalkCoproductBaseChangeIso_summand f g f' g' h_cart ybar' x F))
    sorry

/-- Evaluating the fibre-coproduct base-change isomorphism recovers
`Sigma.whiskerEquiv` of the summand identifications. -/
theorem abelianStalkCoproductBaseChangeIso_app (ybar' : GeometricPoint Y')
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianStalkCoproductBaseChangeIso f g f' g' h_cart ybar').app F =
      Sigma.whiskerEquiv (Fiber.baseChangeEquiv f g f' g' h_cart ybar').symm
        (fun x ↦
          abelianStalkCoproductBaseChangeIso_summand f g f' g' h_cart ybar' x F) :=
  rfl

end AlgebraicGeometry.Scheme.Etale

end
