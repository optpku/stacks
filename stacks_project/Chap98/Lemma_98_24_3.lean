module

public import stacks_project.Chap98.Lemma_98_24_3_NaiveCotangent

/-!
# Existence of a naive cotangent obstruction class

In Situation 98.24.2, compatibility of obstruction classes with the connecting
map of a short exact sequence of deformation situations produces a class
`ξ ∈ H¹(K ⊗^L NL{A⁄Λ})` recovering every `o_x(A')` and matching the canonical
element of Remark 98.21.8.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver
open scoped NaiveCotangent

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

namespace DualObstruction

/-- Lemma 98.24.3. In Situation 98.24.2, assume furthermore that given a short
exact sequence of deformation situations as in Remark 98.21.5 and a lift
`x₂'` of `x` to `A₂'`, the obstruction `o_x(A₃')` equals `∂ θ`, where `θ` is
the class in `H¹(K ⊗^L I₁)` of the restriction `x₂'|Spec(A₁')` via
`A₁' ≃ A[I₁]` and `T_x ≅ H¹(K ⊗^L -)`. Then there exists
`ξ ∈ H¹(K ⊗^L NL{A⁄Λ})` such that `ξ_{A'} = o_x(A')` for every deformation
situation `(x, A' → A)`, and `ξ_can` matches the canonical element of
Remark 98.21.8 via `T_x ≅ H¹(K ⊗^L -)`. -/
@[stacks 07YY]
theorem exists_naiveCotangentClass (𝒟 : DualObstruction X)
    (h : IsConnectingCompatible 𝒟) :
    ∃ ξ : homologyTensorDerived 𝒟.complex 1
        (Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier),
      RecoversObstructions 𝒟 ξ ∧
      ULift.up (𝒟.evalKaehler ξ) =
        𝒟.tangentIso.hom.app 𝒟.kaehler
          (canonicalElement 𝒟.baseHom 𝒟.factor (toFiber 𝒟.toObjectOverSpec)
            inferInstance) :=
  sorry

end DualObstruction

end AlgebraicGeometry.GroupoidsOver
