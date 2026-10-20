module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.PointIntersection
import StacksCheckRecall

universe u

/- 54.15.2.1: The intersection multiplicity at `p` is the length over the ambient
local ring of the local ring of the scheme-theoretic intersection `Y ∩ Z`. -/
@[stacks 0BI6] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.pointIntersectionMultiplicity_def :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      (Y Z : X.IdealSheafData) (p : X),
      Y.pointIntersectionMultiplicity Z p =
        (Module.length (X.presheaf.stalk p)
          (X.presheaf.stalk p ⧸
            (AlgebraicGeometry.Scheme.IdealSheafData.pointIntersectionStalkIdeal Y p ⊔
              AlgebraicGeometry.Scheme.IdealSheafData.pointIntersectionStalkIdeal Z p))))
