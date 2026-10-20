module

public import ReasLib.AlgebraicGeometry.EllipticCurve.WeierstrassFamily

/-!
# The Weierstrass classifying cover of M11

The names M11 and weierstrassCover are the source-facing bridges to the existing moduli stack
of elliptic curves and to the classifying 1-morphism of the universal Weierstrass family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The moduli stack M11 of elliptic curves, as a category fibred in groupoids over
Sch / Spec ℤ. -/
abbrev M11 : GroupoidsOver EllipticCurve.Moduli.specInt :=
  EllipticCurve.moduli

namespace M11

/-- The classifying 1-morphism W to M11 of the universal Weierstrass family
(E_W, f_W, 0_W). -/
def weierstrassCover : GroupoidsOver.slice WeierstrassScheme.overInt ⟶ M11.{u} :=
  WeierstrassScheme.classifying

end M11

end AlgebraicGeometry
