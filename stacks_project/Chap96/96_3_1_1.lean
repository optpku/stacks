/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
public import ReasLib.CategoryTheory.Sites.Presheaf.Pushforward

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u w

variable {S : Scheme.{u}}
variable {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}
variable (f : X ⟶ Y)

/- 96.3.1.1 (1): a 1-morphism f : X ⟶ Y of categories fibred in groupoids over
(Sch/S)_fppf induces the presheaf pullback f^p : PSh(Y) ⥤ PSh(X), realized as
precomposition with (toFunctor f).op. -/
@[stacks 06TK] #check
  (CategoryTheory.Functor.presheafInverseImage (toFunctor f) (Type (max (u + 1) w)) :
    (Y.totalᵒᵖ ⥤ Type (max (u + 1) w)) ⥤
      (X.totalᵒᵖ ⥤ Type (max (u + 1) w)))

/- 96.3.1.1 (2): the matching presheaf pushforward _p f : PSh(X) ⥤ PSh(Y) is the
chosen right Kan extension along (toFunctor f).op. -/
@[stacks 06TK] #check
  (CategoryTheory.Functor.presheafPushforward (toFunctor f) :
    (X.totalᵒᵖ ⥤ Type (max (u + 1) w)) ⥤
      (Y.totalᵒᵖ ⥤ Type (max (u + 1) w)))
