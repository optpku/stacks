module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Finiteness.Projective
public import stacks_project.Chap64.Lemma_64_15_9_Coinvariants
public import stacks_project.Chap64.Lemma_64_15_9_Extension

@[expose] public section

open Ring
open scoped MonoidAlgebra Ring
open MonoidAlgebra LinearMap.FiniteProjective

noncomputable section

universe u v w x

variable {Λ : Type u} {G : Type v} {Γ : Type w}
variable [Ring Λ] [Group G] [Monoid Γ] [Finite G]
variable (S : NatMonoidExtension G Γ) (P : Type x)
variable [AddCommGroup P] [Module (Λ[Γ]) P] [Module (Λ[G]) P] [Module Λ P]
variable [IsScalarTower Λ (Λ[G]) P]
variable [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P]

namespace LinearMap.FiniteProjective

/-- Lemma 64.15.9 (1). Let `P` be a `Λ[Γ]`-module, finite projective as a `Λ[G]`-module.
Then the coinvariants `P_G` form a finite projective `Λ`-module. -/
@[stacks 03UD]
theorem coinvariants_finiteProjective :
    Module.FiniteProjective Λ (Coinvariants Λ G P) := sorry

end LinearMap.FiniteProjective

namespace MonoidAlgebra.Coinvariants

/-- Lemma 64.15.9 (2). The coinvariants `P_G` are endowed with the action of
`1 ∈ ℕ = Γ/G`, as the `Λ`-linear endomorphism `oneEnd`. Powers of this
endomorphism give the action of `ℕ`. -/
@[stacks 03UD]
def oneEnd
    [IsScalarTower Λ (Λ[Γ]) P] [IsRestrictionAlongInl Λ S P] :
    Module.End Λ (Coinvariants Λ G P) :=
  lift Λ G P ((mk Λ G P).comp (smulEnd (S.degreeOneLift).val)) sorry

/-- Every degree-1 element of `Γ` induces the endomorphism `oneEnd` on coinvariants. -/
theorem oneEnd_spec
    [IsScalarTower Λ (Λ[Γ]) P] [IsRestrictionAlongInl Λ S P]
    (γ : S.degreeOne) (p : P) :
    (oneEnd S P : Module.End Λ (Coinvariants Λ G P)) (mk Λ G P p) =
      mk Λ G P ((smulEnd γ.val : Module.End Λ P) p) :=
  sorry

/-- The action of `n : ℕ = Γ/G` on coinvariants is the `n`-th power of `oneEnd`. -/
def natEnd [IsScalarTower Λ (Λ[Γ]) P] [IsRestrictionAlongInl Λ S P]
    (n : ℕ) : Module.End Λ (Coinvariants Λ G P) :=
  oneEnd S P ^ n

end MonoidAlgebra.Coinvariants

namespace LinearMap.FiniteProjective

/-- Lemma 64.15.9 (3). The finite-projective trace of the action of `1 ∈ ℕ` on `P_G`
equals the sum of `Z_γ`-traces `Tr_Λ^{Z_γ}(γ, P)` over `G`-conjugacy classes of
degree-1 elements of `Γ`. -/
@[stacks 03UD]
theorem trace_one_coinvariants
    [IsScalarTower Λ (Λ[Γ]) P] [IsRestrictionAlongInl Λ S P] :
    (traceNatural (Coinvariants.oneEnd S P) : Λ♮) =
      ∑ᶠ c : S.DegreeOneGConjClass, conjClassTrace S P c := sorry

end LinearMap.FiniteProjective
