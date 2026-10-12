/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.InfinitesimalNeighbourhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.InfinitesimalNeighbourhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood

/- Lemma 37.12.3 (1): if every base change of a finite type morphism of locally
Noetherian schemes to an infinitesimal neighbourhood of a closed subscheme is smooth,
then the morphism is smooth at every point lying above that closed subscheme. -/
@[stacks 0A43] #check
  (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.smoothAt_of_smooth_pullbacks :
    ∀ {X S Z : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian S]
      (f : X ⟶ S) [FiniteType f] (i : Z ⟶ S) [IsClosedImmersion i]
      [∀ n : ℕ, Smooth (pullback.snd f (toAmbient i n))]
      (x : X) (_ : f x ∈ Set.range i),
      f.SmoothAt x)

/- Lemma 37.12.3 (2): if every base change of a finite type morphism of locally
Noetherian schemes to an infinitesimal neighbourhood of a closed subscheme is étale,
then the morphism is étale at every point lying above that closed subscheme. -/
@[stacks 0A43] #check
  (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.etaleAt_of_etale_pullbacks :
    ∀ {X S Z : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian S]
      (f : X ⟶ S) [FiniteType f] (i : Z ⟶ S) [IsClosedImmersion i]
      [∀ n : ℕ, Etale (pullback.snd f (toAmbient i n))]
      (x : X) (_ : f x ∈ Set.range i),
      f.EtaleAt x)

end AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood
