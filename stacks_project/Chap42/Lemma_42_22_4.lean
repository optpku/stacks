module

public import ReasLib.AlgebraicGeometry.ChowGroup.Envelope
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 42.22.4: if `f : Y ⟶ X` is an envelope over the universally catenary
dimensioned base `S`, then the sequence from the two projection pushforwards on
`Y ×_X Y`, followed by pushforward along `f`, is exact and ends in zero. -/
@[stacks 0GU8] #check
  (AlgebraicGeometry.ChowGroup.Envelope.exact :
    ∀ {S X Y : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
      [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
      (f : Y ⟶ X) [IsEnvelope f] (k : ℤ),
      (ChowGroup.Descent.complex p δ f k).Exact ∧
        Epi (ChowGroup.Descent.complex p δ f k).g)

end AlgebraicGeometry
