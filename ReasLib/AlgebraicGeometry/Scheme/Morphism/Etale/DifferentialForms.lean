module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.ExteriorPower.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Differentials

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

variable {X' X S' S : Scheme.{u}}
variable {f : X' ⟶ X} {g : S' ⟶ S} {h : X ⟶ S} {h' : X' ⟶ S'}

/-- For an étale commutative square of schemes, the canonical comparison on relative
differential forms is an isomorphism in every exterior degree. -/
instance formComparison_isIso_of_etale (sq : CommSq f h' h g) [Etale f] [Etale g]
    (p : ℕ) : IsIso (formComparison sq p) := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials
