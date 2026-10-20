module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Fiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.35.6: every étale neighbourhood of the distinguished point in the
fibre of `f` is dominated, by an open immersion of pointed étale
neighbourhoods, by the fibre of an étale neighbourhood of the original point. -/
@[stacks 0CAS] #check
  (AlgebraicGeometry.Scheme.EtaleNeighborhood.exists_fiberOpenImmersion :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X)
      (V : AlgebraicGeometry.Scheme.EtaleNeighborhood
        (f.fiber (f x)) (f.asFiber x)),
      ∃ (U : AlgebraicGeometry.Scheme.EtaleNeighborhood X x)
        (h : AlgebraicGeometry.Scheme.EtaleNeighborhood.Hom
          (AlgebraicGeometry.Scheme.EtaleNeighborhood.fiber f U) V),
        AlgebraicGeometry.IsOpenImmersion h.toEtaleHom.left)
