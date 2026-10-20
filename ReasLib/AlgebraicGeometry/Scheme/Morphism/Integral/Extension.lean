module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.IsIntegralHom

/-- A surjective integral morphism over an open subscheme extends to a surjective integral
morphism over the ambient scheme whose pullback is isomorphic to the original morphism. -/
theorem exists_surjective_extension {S V : Scheme.{u}} (U : S.Opens) (p : V ⟶ U)
    [Surjective p] [IsIntegralHom p] :
    ∃ (Vbar : Scheme.{u}) (q : Vbar ⟶ S),
      IsIntegralHom q ∧ Surjective q ∧
        Nonempty (Over.mk (pullback.snd q U.ι) ≅ Over.mk p) := sorry

end AlgebraicGeometry.IsIntegralHom
