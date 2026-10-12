/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Duality
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 42.56.3 (1): every scheme has a dualization ring endomorphism on
its Grothendieck ring of finite locally free modules. -/
@[stacks 0FV8] #check (AlgebraicGeometry.Scheme.VectorBundleK0.dual :
  (X : AlgebraicGeometry.Scheme.{u}) →
    AlgebraicGeometry.Scheme.VectorBundleK0 X →+*
      AlgebraicGeometry.Scheme.VectorBundleK0 X)

/- Lemma 42.56.3 (2): dualization sends the class of a finite locally free
module to the class of its dual. -/
@[stacks 0FV8] #check (AlgebraicGeometry.Scheme.VectorBundleK0.dual_of :
  (X : AlgebraicGeometry.Scheme.{u}) →
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) →
      AlgebraicGeometry.Scheme.VectorBundleK0.dual X
          (ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
          (AlgebraicGeometry.Scheme.VectorBundleK0.dualObj X E))

/- Lemma 42.56.3 (3): dualization commutes with pullback. -/
@[stacks 0FV8] #check (AlgebraicGeometry.Scheme.VectorBundleK0.dual_pullback :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ Y) →
    (AlgebraicGeometry.Scheme.VectorBundleK0.dual X).comp
        (AlgebraicGeometry.Scheme.VectorBundleK0.pullback f) =
      (AlgebraicGeometry.Scheme.VectorBundleK0.pullback f).comp
        (AlgebraicGeometry.Scheme.VectorBundleK0.dual Y))
