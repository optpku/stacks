module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.AlgebraicSpaceComparison
import StacksCheckRecall

/-!
# Maps out of affine formal schemes, algebraic-space targets

For a complete local Noetherian `S`-algebra `R` and an algebraic space `X` over
`S`, morphisms `Spec(R) ⟶ X` over `S` are in bijection with morphisms
`Spf(R) ⟶ X` over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/- Lemma 87.33.3: Let `S` be a scheme. Let `R` be a complete local Noetherian
`S`-algebra. Let `X` be an algebraic space over `S`. Then the natural map
`Mor_S(Spec(R), X) ⟶ Mor_S(Spf(R), X)` is bijective. -/
@[stacks 0AQH] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.specHomToSpfHom_algebraicSpace_bijective :
  ∀ {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsNoetherianRing R] [IsCompleteLocalRing R]
    [TopologicalRing.IsWeaklyAdmissibleRing R]
    (h_adic : IsAdic (maximalIdeal R)) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (X : AlgebraicSpace S),
    Function.Bijective (specHomToSpfHom_algebraicSpace structureHom X))

end AlgebraicGeometry.AffineFormalAlgebraicSpace
