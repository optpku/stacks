module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Pullbacks
import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Factorization

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.IsFinite

/-- A surjective finite morphism over a quasi-compact open subscheme extends to a surjective
finite morphism over the ambient quasi-compact quasi-separated scheme whose pullback is
isomorphic to the original morphism over the open subscheme. -/
theorem exists_surjective_extension {S V : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] (U : S.Opens) [QuasiCompact U.ι] (p : V ⟶ U)
    [Surjective p] [IsFinite p] :
    ∃ (Vbar : Scheme.{u}) (q : Vbar ⟶ S),
      IsFinite q ∧ Surjective q ∧
        Nonempty (Over.mk (pullback.snd q U.ι) ≅ Over.mk p) := sorry

end AlgebraicGeometry.IsFinite
