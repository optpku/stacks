module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowCohomology.Restriction

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 42.34.2: restriction along `f : X ⟶ Y` induces the canonical
contravariant `ℤ`-algebra map `A⁎(Y) → A⁎(X)`, often written `f⁎`. -/
@[stacks 0B7F] #check (@AlgebraicGeometry.ChowCohomology.restrict :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] {Y' Y : Scheme.{u}} {p : Y' ⟶ S} {q : Y ⟶ S}
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] (f : Over.mk p ⟶ Over.mk q),
    AlgebraicGeometry.ChowCohomology.ring delta q →ₐ[ℤ]
      AlgebraicGeometry.ChowCohomology.ring delta p)
