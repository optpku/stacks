module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Proposition 50.14.1: for a rank-r locally free module on X over S, the map
from the finite direct sum of Hᵈᴿ^(q - 2i)(X/S) to Hᵈᴿ^q(P/S), given by
left cup multiplication by canonical powers of c₁ᵈᴿ(𝒪_P(1)) after pullback,
is an isomorphism. -/
@[stacks 0FMT] #check
  (AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle.cohomologyMapIsIso :
    ∀ {S X P : Scheme.{u}} (f : X ⟶ S) (E : X.Modules) (r : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (π : P ⟶ X)
      (hπ : Scheme.ProjectiveBundle.Representation π E) (q : ℤ),
      IsIso (Scheme.DeRham.ProjectiveBundle.cohomologyMap f E r π hπ q))
