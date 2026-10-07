module

import ReasLib.AlgebraicGeometry.Scheme.Blowup.Reduced
import StacksCheckRecall

universe u

/- Lemma 31.32.8: Let `X` be a scheme and `I ⊆ 𝒪_X` a quasi-coherent sheaf of ideals.
If `X` is reduced, then the blowup of `X` in `I` is reduced. -/
@[stacks 0808] #check
  (AlgebraicGeometry.Blowup.isReduced :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {I : X.IdealSheafData}
      (π : AlgebraicGeometry.Blowup X I) [AlgebraicGeometry.IsReduced X],
      AlgebraicGeometry.IsReduced π.scheme)
