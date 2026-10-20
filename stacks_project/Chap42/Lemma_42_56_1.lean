module

import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Adams
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 42.56.1 (1): every scheme has a second Adams ring endomorphism on
its Grothendieck ring of finite locally free modules. -/
@[stacks 0FEJ] #check
  (AlgebraicGeometry.Scheme.VectorBundleK0.adamsTwo :
    (X : AlgebraicGeometry.Scheme.{u}) →
      AlgebraicGeometry.Scheme.VectorBundleK0 X →+*
        AlgebraicGeometry.Scheme.VectorBundleK0 X)

/- Lemma 42.56.1 (2): on an invertible module, the second Adams operation is
the class of its tensor square. -/
@[stacks 0FEJ] #check
  (AlgebraicGeometry.Scheme.VectorBundleK0.adamsTwo_of_invertible :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      (L : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules))
      [AlgebraicGeometry.Scheme.Modules.Invertible L.obj],
      AlgebraicGeometry.Scheme.VectorBundleK0.adamsTwo X
          (ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) L) =
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
          (AlgebraicGeometry.Scheme.VectorBundleK0.tensorObj X L L))

/- Lemma 42.56.1 (3): the second Adams operation commutes with pullback. -/
@[stacks 0FEJ] #check
  (AlgebraicGeometry.Scheme.VectorBundleK0.adamsTwo_pullback :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      (AlgebraicGeometry.Scheme.VectorBundleK0.adamsTwo X).comp
          (AlgebraicGeometry.Scheme.VectorBundleK0.pullback f) =
        (AlgebraicGeometry.Scheme.VectorBundleK0.pullback f).comp
          (AlgebraicGeometry.Scheme.VectorBundleK0.adamsTwo Y))
