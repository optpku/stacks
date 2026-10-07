module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Blowup.Normalized

universe u

/- Definition 54.5.1: for a scheme whose quasi-compact opens have finitely many irreducible
components, a normalized blowup at a closed point is the normalization of the point blowup,
followed by its blowup morphism to the original scheme. -/
@[stacks 0BBS] #check (AlgebraicGeometry.Scheme.NormalizedBlowup :
  AlgebraicGeometry.Scheme.{u} → Type (u + 1))
