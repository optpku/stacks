/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.InfinitesimalNeighbourhood

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood

/-- If every base change of a finite type morphism of locally Noetherian schemes to an
infinitesimal neighbourhood of a closed subscheme is étale, then the morphism is étale at every
point lying above that closed subscheme. -/
theorem etaleAt_of_etale_pullbacks {X S Z : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian S]
    (f : X ⟶ S) [FiniteType f] (i : Z ⟶ S) [IsClosedImmersion i]
    [∀ n : ℕ, Etale (pullback.snd f (toAmbient i n))]
    (x : X) (hx : f x ∈ Set.range i) :
    f.EtaleAt x := sorry

end AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood
