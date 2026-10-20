module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.FinitePushforward
import StacksCheckRecall

/-!
# Stalks of the pushforward along a finite morphism of algebraic spaces

For a finite morphism of algebraic spaces, the stalk of `f_* F` at a geometric point is the
product of the stalks of `F` at the finitely many same-field geometric lifts.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 69.4.2: for a finite morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
and a geometric point `ybar` of `Y`, the small-étale stalk of `f_* F` at `ybar` is the
product of the stalks of `F` at the same-field geometric lifts of `ybar` to `X`. -/
@[stacks 0DK3] #check (AlgebraicGeometry.AlgebraicSpace.finite_pushforward_stalk_product :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    (ybar : GeometricPoint Y) (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
    IsIsomorphic
      (GeometricPoint.stalk ybar ((sheafPushforwardType f).obj F).obj)
      ((x : CategoryTheory.Over.mk ybar.hom ⟶ CategoryTheory.Over.mk f) →
        GeometricPoint.stalk (GeometricPoint.ofHom ybar x.left) F.obj))
