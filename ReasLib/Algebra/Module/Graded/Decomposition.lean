module

public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# External graded modules over internal graded algebras

An external graded module over the homogeneous pieces of an internally graded algebra carries a
canonical module structure over the ambient algebra. The construction first uses the direct-sum
graded action and then restricts scalars along the homogeneous decomposition equivalence.
-/

@[expose] public section

noncomputable section

open scoped DirectSum

universe uι uκ uR uA uM

namespace DirectSum.Gmodule

variable {ι : Type uι} {κ : Type uκ}
variable {R : Type uR} {A : Type uA}
variable [DecidableEq ι] [AddMonoid ι]
variable [DecidableEq κ] [AddAction ι κ]
variable [CommSemiring R] [Semiring A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
variable (M : κ → Type uM) [∀ j, AddCommMonoid (M j)]
variable [DirectSum.Gmodule (fun i ↦ 𝒜 i) M]

/-- The module over an internally graded algebra induced by an explicit graded action on its
homogeneous pieces. -/
@[reducible, stacks 052N "external graded module from an explicit graded action"]
def moduleFor (G : DirectSum.Gmodule (fun i ↦ 𝒜 i) M) : Module A (⨁ j, M j) :=
  @Module.compHom (⨁ i, 𝒜 i) A (⨁ j, M j) inferInstance inferInstance
    (@DirectSum.Gmodule.module ι κ (fun i ↦ 𝒜 i) M inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance G)
    inferInstance (DirectSum.decomposeRingEquiv 𝒜).toRingHom

/-- Under `moduleFor`, a homogeneous scalar acts on a pure summand through the specified graded
scalar action. -/
@[simp, stacks 052N "homogeneous action for an explicit external graded module"]
theorem moduleFor_smul_of (G : DirectSum.Gmodule (fun i ↦ 𝒜 i) M)
    {i : ι} {j : κ} (a : 𝒜 i) (x : M j) :
    (moduleFor 𝒜 M G).toSMul.smul (a : A) (DirectSum.of M j x) =
      DirectSum.of M (i +ᵥ j)
        (G.toGdistribMulAction.toGMulAction.toGSMul.smul a x) := sorry

/-- The module over an internally graded algebra induced by the external graded-module action on
its homogeneous pieces. -/
@[reducible, stacks 052N "external graded module over an internal graded algebra"]
def moduleOfDecomposition : Module A (⨁ j, M j) :=
  moduleFor 𝒜 M inferInstance

/-- Under `moduleOfDecomposition`, a homogeneous scalar acts on a pure summand through the
original graded scalar action. -/
@[simp, stacks 052N "homogeneous action in the decomposed external module"]
theorem moduleOfDecomposition_smul_of {i : ι} {j : κ}
    (a : 𝒜 i) (x : M j) :
    (moduleOfDecomposition 𝒜 M).toSMul.smul (a : A) (DirectSum.of M j x) =
      DirectSum.of M (i +ᵥ j)
        (GradedMonoid.GSMul.smul (A := fun n ↦ 𝒜 n) (M := M) a x) := sorry

end DirectSum.Gmodule
