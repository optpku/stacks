module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Artin
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Scheme.Over

/- Proposition 98.16.1. A functor satisfying Artin's axioms over a locally
Noetherian scheme with G-ring stalks at finite-type points is an algebraic space. -/
@[stacks 07Y1] #check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_artinAxioms :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {F : (Over S)ᵒᵖ ⥤ Type u} (hΔ : representableByAlgebraicSpaces (diag F))
    (h_size : boundedOnFiniteTypeFields F)
    (h0 : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (h1 : PreservesDirectedAffineLimits S F)
    (hRS : GroupoidsOver.HasRimSchlessinger (toGroupoidsOver F))
    (hT : GroupoidsOver.HasFiniteDimensionalPredeformations (toGroupoidsOver F))
    (h_eff : ∀ ξ : GroupoidsOver.FormalObject (toGroupoidsOver F),
      GroupoidsOver.FormalObject.IsEffective ξ)
    (h_open : GroupoidsOver.OpennessOfVersality (toGroupoidsOver F))
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)),
    IsAlgebraicSpace F)

end AlgebraicGeometry.AlgebraicSpace
