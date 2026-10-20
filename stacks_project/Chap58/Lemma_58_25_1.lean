module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.PrincipalQuotientPurity
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.PuncturedSpectrum
open IsLocalRing

noncomputable section

universe u

/- Lemma 58.25.1: for a Noetherian local ring `A` and `f` in its maximal ideal,
if `A` admits a dualizing complex and is `f`-adically complete, either `A_f`
satisfies `(S₂)` and every irreducible component not contained in `V(f)` has
dimension at least four, or every prime outside `V(f)` whose closure meets
`V(f)` beyond the closed point has depth plus quotient dimension greater than
three, purity holds at `(A_f)_p` for every maximal ideal `p` of `A_f`, and
purity holds for `A`, then purity holds for `A ⧸ principalIdeal (f : A)`. -/
@[stacks 0DXZ] #check
  (AlgebraicGeometry.PuncturedSpectrum.hasPurity_principalQuotient_of_dualizing_complete :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (f : maximalIdeal A)
      [Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizing)]
      [IsAdicComplete (principalIdeal (f : A)) A]
      [Fact (dualizingCompleteNeighborhoodAlternative f)]
      [Fact (hasPurityAtMaximalsAway f)]
      [HasPurity A],
      HasPurity (A ⧸ principalIdeal (f : A)))
