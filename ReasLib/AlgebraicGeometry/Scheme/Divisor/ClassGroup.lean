module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Principal
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# The Weil divisor class group

The Weil divisor class group is the quotient of Weil divisors by the subgroup of principal Weil
divisors.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]

/-- A Weil divisor is principal when its coefficients are the orders of a function-field unit. -/
def IsPrincipalWeilDivisor (D : Div(X)) : Prop :=
  ∃ f : X.functionFieldˣ,
    ∀ Z : PrimeDivisor X, D.coeff Z = X.ord (f : X.functionField) Z.genericPoint

/-- The subgroup of principal Weil divisors. -/
def principalWeilDivisors : AddSubgroup (Div(X)) where
  carrier := IsPrincipalWeilDivisor X
  zero_mem' := by
    refine ⟨1, fun Z ↦ ?_⟩
    exact congrArg (fun D : Div(X) ↦ D.coeff Z) (Scheme.principalWeilDivisor_one X).symm
  add_mem' hD hE := by
    obtain ⟨f, hf⟩ := hD
    obtain ⟨g, hg⟩ := hE
    refine ⟨f * g, fun Z ↦ ?_⟩
    rw [WeilDivisor.coeff_add, hf Z, hg Z]
    exact congrArg (fun D : Div(X) ↦ D.coeff Z)
      (Scheme.principalWeilDivisor_mul X f g).symm
  neg_mem' hD := by
    obtain ⟨f, hf⟩ := hD
    refine ⟨f⁻¹, fun Z ↦ ?_⟩
    rw [WeilDivisor.coeff_neg, hf Z]
    exact congrArg (fun D : Div(X) ↦ D.coeff Z)
      (Scheme.principalWeilDivisor_inv X f).symm

notation "Prin(" X ")" => principalWeilDivisors X

/-- Membership in the principal-divisor subgroup is the coefficientwise principal-divisor
condition. -/
theorem mem_principalWeilDivisors_coeff_iff (D : Div(X)) :
    D ∈ Prin(X) ↔
      ∃ f : X.functionFieldˣ,
        ∀ Z : PrimeDivisor X, D.coeff Z = X.ord (f : X.functionField) Z.genericPoint :=
  Iff.rfl

/-- The principal Weil divisor of a function-field unit belongs to `Prin(X)`. -/
theorem principalWeilDivisor_mem_principalWeilDivisors (f : X.functionFieldˣ) :
    Scheme.principalWeilDivisor X f ∈ Prin(X) := by
  exact ⟨f, fun _ ↦ rfl⟩

/-- The Weil divisor class group is the quotient of Weil divisors by principal Weil divisors. -/
abbrev WeilDivisorClassGroup : Type u :=
  Div(X) ⧸ Prin(X)

notation "Cl(" X ")" => WeilDivisorClassGroup X

/-- The canonical quotient homomorphism from Weil divisors to the divisor class group. -/
abbrev weilDivisorClassGroupMk : Div(X) →+ Cl(X) :=
  QuotientAddGroup.mk' (Prin(X))

/-- The quotient map `Div(X) → Cl(X)` is surjective. -/
theorem weilDivisorClassGroupMk_surjective :
    Function.Surjective (weilDivisorClassGroupMk X) := by
  simpa using (QuotientAddGroup.mk'_surjective (Prin(X)))

/-- The principal-divisor map followed by the Weil divisor class quotient forms a right-exact
sequence. -/
theorem weilDivisorClass_exactSequence :
    Function.Exact (Scheme.principalWeilDivisor X) (weilDivisorClassGroupMk X) ∧
      Function.Surjective (weilDivisorClassGroupMk X) := sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.Curve

/-- The Weil divisor class group of a curve is the quotient of its Weil divisors by its
principal Weil divisors. -/
noncomputable abbrev classGroup {k : Type u} [Field k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] : Type u :=
  @AlgebraicGeometry.WeilDivisorClassGroup X.left
    (LocallyOfFiniteType.isLocallyNoetherian X.hom) inferInstance

end AlgebraicGeometry.Curve
