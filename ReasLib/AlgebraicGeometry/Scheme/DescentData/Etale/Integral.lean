module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale.QCSeparated

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor

/-- For a surjective integral morphism `f : X ⟶ S`, the canonical functor from
quasi-compact separated schemes étale over `S` to étale descent data relative to `f`
with quasi-compact separated component is an equivalence. -/
instance qcSeparatedIsEquivalence {X S : Scheme.{u}} (f : X ⟶ S)
    [Surjective f] [IsIntegralHom f] :
    (qcSeparated f).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor
