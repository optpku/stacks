module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.SquareMorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

universe u

/- Remark 67.19.4: the quotient of the affine line by punctured negation has a
morphism to the affine line induced by coordinate squaring. -/
@[stacks 05VS] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.toAffineLine :
    ∀ (k : Type u) [Field k], sheafOfPoints k ⟶
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k))
