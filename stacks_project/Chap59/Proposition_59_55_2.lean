module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FinitePushforward
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

@[expose] public section

noncomputable section

universe u

/- Proposition 59.55.2 (1): for a finite morphism `f : X ⟶ Y` and a geometric
point `ybar : Spec k ⟶ Y`, the small-étale stalk of `f_* F` at `ybar` is the
product of the stalks of `F` at the `Spec k`-points of `X` over `ybar`. -/
@[stacks 03QP] #check (AlgebraicGeometry.Scheme.Etale.finitePushforward_stalk_product :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology (Type u)),
    IsIsomorphic
      ((GeometricPoint.toSmallEtalePoint ybar).sheafFiber.obj
        (((smallEtalePullback f).sheafPushforwardContinuous (Type u)
          Y.smallEtaleTopology X.smallEtaleTopology).obj F))
      (piObj (fun x : GeometricPoint.Fiber f ybar =>
        (GeometricPoint.toSmallEtalePoint x.point).sheafFiber.obj F)))

/- Proposition 59.55.2 (2): for a finite morphism `f : X ⟶ Y` and a geometric
point `ybar : Spec k ⟶ Y`, the small-étale stalk of `f_* F` at `ybar` is the
direct sum of the stalks of `F` at the `Spec k`-points of `X` over `ybar`. -/
@[stacks 03QP] #check (AlgebraicGeometry.Scheme.Etale.finitePushforward_stalk_coprod :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    IsIsomorphic
      ((GeometricPoint.toSmallEtalePoint ybar).sheafFiber.obj
        (((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
          Y.smallEtaleTopology X.smallEtaleTopology).obj F))
      (sigmaObj (fun x : GeometricPoint.Fiber f ybar =>
        (GeometricPoint.toSmallEtalePoint x.point).sheafFiber.obj F)))

/- Proposition 59.55.2 (3): for a finite morphism `f : X ⟶ Y` and every
abelian étale sheaf `F` on `X`, the higher direct images `R^q f_* F` vanish
for `q ≥ 1`. -/
@[stacks 03QP] #check (AlgebraicGeometry.Scheme.Etale.finiteHigherDirectImage_isZero :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ), 0 < q →
    IsZero
      (higherDirectImage (smallEtalePullback f) F q :
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))
