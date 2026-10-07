module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Effective
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.UniqueFactorization
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.OpenComplement.Dimension

/-!
# Effective Cartier divisors with prescribed open complement

Existence of effective Cartier divisors whose support is the complement of a dense affine open.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.OpenComplement

/-- A dense open with affine inclusion in a Noetherian scheme whose local rings off the open are
unique factorization domains is the open complement of an effective Cartier divisor. -/
theorem exists_effectiveCartierDivisor_of_isAffineHom
    {X : Scheme.{u}} [IsNoetherian X] {U : X.Opens} [IsAffineHom U.ι]
    (hU_dense : Dense (U : Set X))
    (hUFD : ∀ x : X, x ∉ (U : Set X) → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ D : X.IdealSheafData,
      IsEffectiveCartierDivisor D.subschemeι ∧ U = D.openComplement := sorry

/-- A dense affine open in a Noetherian separated scheme whose local rings off the open are
unique factorization domains is the open complement of an effective Cartier divisor. -/
theorem exists_effectiveCartierDivisor_of_isSeparated
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated] {U : X.Opens}
    (hU : IsAffineOpen U) (hU_dense : Dense (U : Set X))
    (hUFD : ∀ x : X, x ∉ (U : Set X) → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ D : X.IdealSheafData,
      IsEffectiveCartierDivisor D.subschemeι ∧ U = D.openComplement := sorry

/-- A dense affine open in a Noetherian scheme with affine diagonal whose local rings off the
open are unique factorization domains is the open complement of an effective Cartier divisor. -/
theorem exists_effectiveCartierDivisor_of_affineDiagonal
    {X : Scheme.{u}} [IsNoetherian X]
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] {U : X.Opens}
    (hU : IsAffineOpen U) (hU_dense : Dense (U : Set X))
    (hUFD : ∀ x : X, x ∉ (U : Set X) → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ D : X.IdealSheafData,
      IsEffectiveCartierDivisor D.subschemeι ∧ U = D.openComplement := sorry

end AlgebraicGeometry.Scheme.OpenComplement
