module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

namespace FormallyEtale

/-- Every formally étale scheme morphism is formally smooth. -/
instance toFormallySmooth [FormallyEtale f] : FormallySmooth f := sorry

/-- A scheme morphism is formally étale exactly when it is formally smooth and formally
unramified. -/
theorem iff_formallySmooth_and_formallyUnramified :
    FormallyEtale f ↔ FormallySmooth f ∧ FormallyUnramified f := sorry

end FormallyEtale

end AlgebraicGeometry
