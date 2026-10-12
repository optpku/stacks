/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.Algebra.Category.Grp.Colimits
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import ReasLib.CategoryTheory.Sites.HigherDirectImage

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

/-- The geometric stalk of the pushforward of a set-valued étale sheaf along a finite
morphism is isomorphic to the product of its stalks over the same-field geometric fiber. -/
theorem finitePushforward_stalk_product (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    IsIsomorphic
      ((GeometricPoint.toSmallEtalePoint ybar).sheafFiber.obj
        (((smallEtalePullback f).sheafPushforwardContinuous (Type u)
          Y.smallEtaleTopology X.smallEtaleTopology).obj F))
      (piObj (fun x : GeometricPoint.Fiber f ybar =>
        (GeometricPoint.toSmallEtalePoint x.point).sheafFiber.obj F)) := sorry

/-- The geometric stalk of the pushforward of an abelian étale sheaf along a finite
morphism is isomorphic to the coproduct of its stalks over the same-field geometric fiber. -/
theorem finitePushforward_stalk_coprod (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIsomorphic
      ((GeometricPoint.toSmallEtalePoint ybar).sheafFiber.obj
        (((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
          Y.smallEtaleTopology X.smallEtaleTopology).obj F))
      (sigmaObj (fun x : GeometricPoint.Fiber f ybar =>
        (GeometricPoint.toSmallEtalePoint x.point).sheafFiber.obj F)) := sorry

/-- All positive higher direct images of an abelian étale sheaf along a finite
morphism of schemes are zero. -/
theorem finiteHigherDirectImage_isZero
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) (hq : 0 < q) :
    IsZero
      (higherDirectImage (smallEtalePullback f) F q :
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) := sorry

end AlgebraicGeometry.Scheme.Etale
