module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood
import StacksCheckRecall

universe u

/- Definition 37.35.1 (1): an étale neighbourhood of `(S, s)` is an étale `S`-scheme
together with a selected point lying over `s`. -/
@[stacks 02LE] #check (AlgebraicGeometry.Scheme.EtaleNeighborhood :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) (s : S), Type (u + 1))

/- Definition 37.35.1 (2): a morphism of étale neighbourhoods is a morphism of their
étale `S`-schemes that preserves the selected points. -/
@[stacks 02LE] #check (AlgebraicGeometry.Scheme.EtaleNeighborhood.Hom :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {s : S},
    AlgebraicGeometry.Scheme.EtaleNeighborhood S s →
      AlgebraicGeometry.Scheme.EtaleNeighborhood S s → Type u)

/- Definition 37.35.1 (3): an elementary étale neighbourhood induces an isomorphism
between the residue fields at its base and selected points. -/
@[stacks 02LE] #check (AlgebraicGeometry.Scheme.EtaleNeighborhood.IsElementary :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {s : S},
    AlgebraicGeometry.Scheme.EtaleNeighborhood S s → Prop)
