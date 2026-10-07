module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Blowup.Splitting
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.IsBlowup.DeRham

universe u

/- Proposition 50.17.3: the canonical relative de Rham comparison for a blowup of a
smooth scheme along a smooth center admits a retraction in the coefficient-derived category. -/
@[stacks 0FUW] #check
  (AlgebraicGeometry.IsBlowup.DeRham.toBlowup_isSplitMono :
    ∀ {S X X' : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
      [Smooth f] [Smooth (I.subschemeι ≫ f)] [IsBlowup b I],
      IsSplitMono (toBlowup f I b))
