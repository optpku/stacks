module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.InfinitesimalNeighbourhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleAt

/-!
# Étaleness from infinitesimal neighbourhoods

A locally finite-type morphism of algebraic spaces to a locally Noetherian
target is étale above a closed subspace if its base changes to all
infinitesimal neighbourhoods of that subspace are étale.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood

/-- If every base change of a locally finite-type morphism of algebraic spaces
to an infinitesimal neighbourhood of a closed subspace of a locally Noetherian
target is étale, then the morphism is étale at every point lying above that
closed subspace. -/
theorem etaleAt_of_etale_pullbacks {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (i : Z ⟶ Y) [IsClosedImmersion i]
    [∀ n : ℕ, Etale (pullback.snd f (toAmbient i n))]
    (x : Points X) (hx : Points.map f x ∈ Set.range (Points.map i)) :
    EtaleAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood
