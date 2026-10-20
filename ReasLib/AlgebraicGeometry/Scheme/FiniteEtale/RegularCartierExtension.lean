module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.RegularExtension
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Complement
public import ReasLib.AlgebraicGeometry.Scheme.Regular

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The open complement of an effective Cartier divisor is dense. -/
theorem dense_closedImmersionComplement {X D : Scheme.{u}} (i : D ⟶ X)
    [IsEffectiveCartierDivisor i] :
    Dense ((closedImmersionComplement i : Set X)) := sorry

/-- Every ambient stalk along a regular effective Cartier divisor on a locally Noetherian scheme
is a regular local ring. -/
theorem isRegularLocalRing_stalk_of_regularCartierComplement {X D : Scheme.{u}}
    [IsLocallyNoetherian X] (i : D ⟶ X) [IsEffectiveCartierDivisor i] [Scheme.Regular D]
    (x : X) (hx : x ∉ (closedImmersionComplement i : Set X)) :
    IsRegularLocalRing (X.presheaf.stalk x) := sorry

/-- The complement of a regular effective Cartier divisor on a locally Noetherian scheme has
discrete-valuation boundary stalks. -/
instance hasDVRBoundary_of_regularCartierComplement {X D : Scheme.{u}}
    [IsLocallyNoetherian X] (i : D ⟶ X) [IsEffectiveCartierDivisor i] [Scheme.Regular D] :
    HasDVRBoundary X (closedImmersionComplement i) := sorry

/-- A finite étale cover of the complement of a regular effective Cartier divisor on a locally
Noetherian scheme extends over the whole scheme if it is unramified in codimension one. -/
theorem exists_extension_of_unramifiedInCodimensionOne_of_regularCartier
    {X D : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X)
    [IsEffectiveCartierDivisor i] [Scheme.Regular D]
    (Y : Scheme.FiniteEtale (closedImmersionComplement i).toScheme)
    (hY : IsUnramifiedInCodimensionOne (closedImmersionComplement i)
      (dense_closedImmersionComplement i) Y) :
    ∃ Y' : Scheme.FiniteEtale X,
      Nonempty ((finiteEtaleBaseChange (closedImmersionComplement i).ι).obj Y' ≅ Y) := sorry

end AlgebraicGeometry.Scheme.FiniteEtale
