/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure

/-!
# Base change of reduced point closures

This file provides the canonical comparison from the base change of a reduced
point closure to the corresponding base change of the ambient scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PointClosure

/-- The base change of a reduced point closure maps canonically to the base change of its
ambient scheme. -/
def baseChangeMap {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (y : X) :
    pullback g (ι y ≫ f) ⟶ pullback g f :=
  pullback.map g (ι y ≫ f) g f (𝟙 S') (ι y) (𝟙 S)
    ((Category.comp_id g).trans (Category.id_comp g).symm) (Category.comp_id _)

end AlgebraicGeometry.Scheme.PointClosure
