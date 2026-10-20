module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.TopologicalInvariance
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- 59.45.2.1 -/
@[stacks 04E0] #check
  (AlgebraicGeometry.Scheme.AffineEtale.exists_pullback_iso_of_universalHomeomorphism :
    ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [UniversalHomeomorphism f]
      (U : X.AffineEtale),
      ∃ V : Y.AffineEtale,
        Nonempty ((Scheme.smallEtalePullback f).obj ((Scheme.AffineEtale.Spec Y).obj V) ≅
          (Scheme.AffineEtale.Spec X).obj U))
