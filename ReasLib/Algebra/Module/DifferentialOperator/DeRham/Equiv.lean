module

public import ReasLib.Algebra.Module.DifferentialOperator.DeRham

/-!
# Transport of Exterior-Power de Rham Families

This leaf transports degree-raising exterior-form families along linear
equivalences.  It is independent of a particular presentation of the module,
so Kähler base change and other comparison isomorphisms use the same owner.

@stack 0H8Y
-/

@[expose] public section

universe u v

namespace DifferentialOperator.DeRham

section

variable {R : Type u} {S : Type v} {M : Type v} {N : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

namespace Family

/-- The exterior-power differential family obtained by conjugating `δ` along
an `S`-linear equivalence from `M` to `N`. -/
@[stacks 0H8Y]
noncomputable def transport
    (e : M ≃ₗ[S] N) (δ : Family R S M) : Family R S N :=
  fun p ↦
    (exteriorPower.form.mapRestrictScalars R e.toLinearMap (p + 1)).comp
      ((δ p).comp (exteriorPower.form.mapRestrictScalars R e.symm.toLinearMap p))

/-- The transported family intertwines with its source family through the
given linear equivalence. -/
@[stacks 0H8Y]
theorem transport_descends
    (e : M ≃ₗ[S] N) (δ : Family R S M) :
    Descends e.toLinearMap δ (transport e δ) := sorry

/-- The source family intertwines with its transport through the inverse of
the given linear equivalence. -/
@[stacks 0H8Y]
theorem transport_descends_symm
    (e : M ≃ₗ[S] N) (δ : Family R S M) :
    Descends e.symm.toLinearMap (transport e δ) δ := sorry

/-- Transport preserves the exterior-power formulas for the derivation
obtained by composing with the linear equivalence. -/
@[stacks 0H8Y]
theorem transport_satisfiesFormula
    {D : Derivation R S M}
    (e : M ≃ₗ[S] N) (δ : Family R S M)
    (hδ : SatisfiesFormula D δ) :
    SatisfiesFormula (e.toLinearMap.compDer D) (transport e δ) := sorry

/-- Transport preserves the square-zero relation of a differential family. -/
@[stacks 0H8Y]
theorem transport_squaresToZero
    (e : M ≃ₗ[S] N) (δ : Family R S M)
    (hδ : SquaresToZero δ) :
    SquaresToZero (transport e δ) := sorry

/-- Transport preserves the structure of a de Rham differential family. -/
@[stacks 0H8Y]
theorem transport_isDifferential
    {D : Derivation R S M}
    (e : M ≃ₗ[S] N) (δ : Family R S M)
    (hδ : IsDifferential D δ) :
    IsDifferential (e.toLinearMap.compDer D) (transport e δ) := sorry

end Family

end

end DifferentialOperator.DeRham
