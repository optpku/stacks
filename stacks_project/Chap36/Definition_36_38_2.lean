module

public import ReasLib.AlgebraicGeometry.Scheme.K0
import StacksCheckRecall

universe u

/- Definition 36.38.2 (1): for a scheme `X`, `K0 X` is the zeroth Grothendieck group of
the triangulated category of perfect derived `O_X`-modules. -/
@[stacks 0FDG] #check
  (AlgebraicGeometry.Scheme.K0 : AlgebraicGeometry.Scheme.{u} → Type (u + 1))

/- Definition 36.38.2 (2): for a locally Noetherian scheme `X`, `K0' X` is the zeroth
Grothendieck group of coherent `O_X`-modules. -/
@[stacks 0FDG] #check
  (AlgebraicGeometry.Scheme.K0' :
    (X : AlgebraicGeometry.Scheme.{u}) →
      [AlgebraicGeometry.IsLocallyNoetherian X] → Type (u + 1))
