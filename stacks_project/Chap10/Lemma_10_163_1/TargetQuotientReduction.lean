/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.QuotientByIdeal.Mapped
public import ReasLib.RingTheory.Depth.RegularSequence
public import ReasLib.RingTheory.RingHom.Fiber.Quotient
public import ReasLib.RingTheory.Sequence.Regularity
import StacksCheckRecall

@[expose] public section

/-!
Closed-fiber quotient reduction support for Lemma 10.163.1.
@stack 0338
-/

open RingTheory Sequence Ideal IsLocalRing
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct Pointwise Algebra.TensorProduct.Right

universe u v w x uA uP

section

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N] [Module.Flat R N]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] N

/-- Helper for Lemma 10.163.1: quotienting the tensor product by a target element agrees with
tensoring the source module against the target quotient. -/
noncomputable def tensor_quotient_by_target_element
    {M' : Type w} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    {N' : Type x} [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    [Module.Finite S N'] (f : S) :
    QuotSMulTop f (N' ⊗[R] M') ≃ₗ[S] QuotSMulTop f N' ⊗[R] M' := by
  let e₀ :
      ((S ⊗[R] M') ⊗[S] N') ≃ₗ[S] (N' ⊗[R] M') :=
    (TensorProduct.comm S (S ⊗[R] M') N').trans <|
      TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N' M'
  let e₁ :
      QuotSMulTop f (N' ⊗[R] M') ≃ₗ[S]
        QuotSMulTop f ((S ⊗[R] M') ⊗[S] N') :=
    QuotSMulTop.congr f e₀.symm
  let e₂ :
      QuotSMulTop f ((S ⊗[R] M') ⊗[S] N') ≃ₗ[S]
        QuotSMulTop f (N' ⊗[S] (S ⊗[R] M')) :=
    QuotSMulTop.congr f (TensorProduct.comm S (S ⊗[R] M') N')
  let e₃ :
      QuotSMulTop f (N' ⊗[S] (S ⊗[R] M')) ≃ₗ[S]
        QuotSMulTop f N' ⊗[S] (S ⊗[R] M') :=
    (QuotSMulTop.quotSMulTopTensorEquivQuotSMulTop
      (r := f) (M' := N') (M := S ⊗[R] M')).symm
  let e₄ :
      QuotSMulTop f N' ⊗[S] (S ⊗[R] M') ≃ₗ[S]
        QuotSMulTop f N' ⊗[R] M' :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (QuotSMulTop f N') M'
  -- Proof comment: commute the tensor factors until the quotientable `N'` sits on the left,
  -- push the quotient through that factor, and then cancel the auxiliary base change again.
  exact e₁.trans (e₂.trans (e₃.trans e₄))

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsNoetherianRing R] [IsNoetherianRing S] in
/-- Helper for Lemma 10.163.1: if `f` is regular on `N` and `N / fN` stays flat over `R`, then
`f` is also regular on `N ⊗[R] M`. -/
lemma target_regular_on_tensor
    {M' : Type w} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    {N' : Type x} [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    [Module.Finite S N'] {f : S}
    (hreg : IsSMulRegular N' f) (hflat : Module.Flat R (QuotSMulTop f N')) :
    IsSMulRegular (N' ⊗[R] M') f := sorry
/-- Helper for Lemma 10.163.1: quotienting the target module by a closed-fiber regular element
lowers the closed-fiber depth by one. -/
lemma closed_fiber_depth_after_target_quotient
    {N' : Type x} [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    [Module.Finite S N'] [Module.Flat R N'] {f : S}
    (hf : f ∈ maximalIdeal S)
    (hreg : IsSMulRegular (ClosedFiber ⊗[S] N') (algebraMap S ClosedFiber f)) :
    moduleDepth ClosedFiber (ClosedFiber ⊗[S] QuotSMulTop f N') =
      moduleDepth ClosedFiber (ClosedFiber ⊗[S] N') - 1 := sorry
end

@[stacks 0338 "tensor quotient by a target element"]
#check @tensor_quotient_by_target_element
@[stacks 0338 "regularity after tensoring"]
#check @target_regular_on_tensor
@[stacks 0338 "closed-fiber depth drop after quotient"]
#check @closed_fiber_depth_after_target_quotient
