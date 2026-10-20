module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.InfinitesimalNeighbourhood
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 37.12.4: if every base change of a morphism of locally Noetherian schemes
to an infinitesimal neighbourhood of a closed subscheme is flat, then the morphism
is flat at every point lying above that closed subscheme. -/
@[stacks 0D4G] #check
  (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.flatAt_of_flat_pullbacks :
    ∀ {X S Z : Scheme.{u}}
      [IsLocallyNoetherian X] [IsLocallyNoetherian S]
      (f : X ⟶ S) (i : Z ⟶ S) [IsClosedImmersion i]
      [∀ n : ℕ,
        Flat
          (pullback.snd f
            (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.toAmbient i n))]
      (x : X), f x ∈ Set.range i → f.flatAt x)
