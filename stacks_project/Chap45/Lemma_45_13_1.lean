module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Lambda
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 45.13.1 (1): `lambda X r` sends the class of a finite locally free module to
the class of its `r`-th exterior power. -/
@[stacks 0FIC] #check
  (AlgebraicGeometry.Scheme.VectorBundleK0.lambda_of :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) (r : ℕ)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)),
      AlgebraicGeometry.Scheme.VectorBundleK0.lambda X r
          (ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
          (AlgebraicGeometry.Scheme.VectorBundleK0.exteriorPowerObj X E r))

/- Lemma 45.13.1 (2): the operations `lambda X r` commute with pullback of schemes. -/
@[stacks 0FIC] #check
  (AlgebraicGeometry.Scheme.VectorBundleK0.lambda_pullback :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (r : ℕ)
      (a : AlgebraicGeometry.Scheme.VectorBundleK0 Y),
      AlgebraicGeometry.Scheme.VectorBundleK0.pullback f
          (AlgebraicGeometry.Scheme.VectorBundleK0.lambda Y r a) =
        AlgebraicGeometry.Scheme.VectorBundleK0.lambda X r
          (AlgebraicGeometry.Scheme.VectorBundleK0.pullback f a))
