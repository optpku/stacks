module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import ReasLib.Algebra.Group.Action.NatInt
public import ReasLib.Algebra.Module.Graded.HomogeneousMap
public import ReasLib.Algebra.Module.Graded.Quotient.RestrictScalars
public import ReasLib.Algebra.Module.Graded.Span
public import ReasLib.Algebra.Module.Graded.Span.Finite
import StacksCheckRecall

/-!
# Graded Nakayama lemmas

@stack 0EKB
-/

@[expose] public section

open scoped DirectSum
open HomogeneousIdeal

universe uR uA uM uN

variable {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN}
variable [CommSemiring R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
variable (𝒶 : ℕ → Submodule R A)

-- Local declaration justification (source-local notation): `S₊` is the named irrelevant ideal
-- in all four clauses of Lemma 10.56.1; the notation introduces no data or instances.
local notation "S₊" => (HomogeneousIdeal.irrelevant 𝒶)

section GradedModule

variable (ℳ : ℤ → Submodule R M)
variable [GradedAlgebra 𝒶] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒶 ℳ]

/-- Canonical zero-module view of Lemma 10.56.1 (1). -/
@[stacks 0EKB "(1), canonical zero-module view"]
theorem subsingleton_of_irrelevant_ideal_smul_top_eq_top
    (ℳ' : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ'] [SetLike.GradedSMul 𝒶 ℳ']
    [Module.Finite A M]
    (hM : S₊.toIdeal • (⊤ : Submodule A M) = ⊤) :
    Subsingleton M := sorry

/-- **Lemma 10.56.1 (1)** ([Stacks tag 0EKB](https://stacks.math.columbia.edu/tag/0EKB)):
if `S₊ M = M` and `M` is finite, then `M = 0`. -/
@[stacks 0EKB "(1), vanishing"]
theorem eq_bot_of_irrelevant_ideal_smul_eq_top
    (ℳ' : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ'] [SetLike.GradedSMul 𝒶 ℳ']
    [Module.Finite A M]
    (hM : S₊.toIdeal • (⊤ : Submodule A M) = ⊤) :
    (⊤ : Submodule A M) = ⊥ := sorry

/-- **Lemma 10.56.1 (2)**: if `M = N + S₊ N'`, where `N` and `N'` are graded and
`N'` is finite, then `N = M`. -/
@[stacks 0EKB "(2), graded submodule"]
theorem eq_top_of_sup_irrelevant_ideal_smul_eq_top
    {N N' : Submodule A M}
    (hN : N.IsHomogeneous ℳ)
    (hN' : N'.IsHomogeneous ℳ)
    (hN'fg : N'.FG)
    (hM : N ⊔ S₊.toIdeal • N' = ⊤) :
    N = ⊤ := sorry

end GradedModule

section GradedLinearMap

variable (ℳ : ℤ → Submodule R M) (ℕₘ : ℤ → Submodule R N)
variable [GradedAlgebra 𝒶]
variable [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒶 ℳ]
variable [DirectSum.Decomposition ℕₘ] [SetLike.GradedSMul 𝒶 ℕₘ]

/-- **Lemma 10.56.1 (3)**: a map of graded modules is surjective if its reduction modulo
`S₊` is surjective and the target is finite. -/
@[stacks 0EKB "(3), surjectivity"]
theorem surjective_of_irrelevant_reduceModIdeal_surjective
    (f : N →ₗ[A] M)
    (hf : ∀ i, Set.MapsTo f (ℕₘ i) (ℳ i))
    [Module.Finite A M]
    (hquot : Function.Surjective (f.reduceModIdeal S₊.toIdeal)) :
    Function.Surjective f := sorry

end GradedLinearMap

section GradedModule

variable (ℳ : ℤ → Submodule R M)
variable [GradedAlgebra 𝒶] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒶 ℳ]

/-- **Lemma 10.56.1 (4)**: homogeneous elements generating `M/S₊M` already generate the
finite graded module `M`. -/
@[stacks 0EKB "(4), homogeneous generators"]
theorem span_eq_top_of_quotient_span_eq_top_of_homogeneous
    [Module.Finite A M]
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    (hspan :
      Submodule.span A
        ((S₊.toIdeal • (⊤ : Submodule A M)).mkQ '' (s : Set M)) = ⊤) :
    Submodule.span A (s : Set M) = ⊤ := sorry

end GradedModule

@[stacks 0EKB "homogeneous-span owner"]
#check @Submodule.FG.exists_finset_homogeneous_span_eq

@[stacks 0EKB "restricted-scalar quotient grading"]
#check @DirectSum.Decomposition.quotientGradingRestrictScalars

@[stacks 0EKB "homogeneous-map range"]
#check @GradedModule.MapsTo.range_isHomogeneous_of_linearMap

#check @LinearMap.reduceModIdeal
