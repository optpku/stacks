module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Graded.Degreewise
public import ReasLib.RingTheory.AdicCompletion.InverseSystem
public import ReasLib.RingTheory.AdicCompletion.QuotientSystem.Presentation

/-!
# Graded Positive Adic Inverse Systems

This leaf contains the graded structures and comparison statements built on
the positive adic quotient-system API.  The ungraded quotient tower and its
completion comparison live in the sibling `AdicCompletion` leaves.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomogeneousIdeal

noncomputable section

universe u v

namespace AdicCompletion.Graded

variable {A : Type u} [CommRing A]
-- The internal graded-ring pieces are `ℤ`-submodules, matching Mathlib's canonical model for
-- ordinary commutative rings and allowing polynomial gradings (whose pieces are not `A`-ideals).
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- A finite graded module whose positive ideal-power quotient tower realizes
a prescribed positive inverse system of graded modules. -/
@[stacks 0EKC "graded adic quotient realization"]
structure Realization
    (I : HomogeneousIdeal 𝒜)
    (G : PNatInverseSystem (ModuleCat.{v} A))
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G.stage n))
    extends toPresentation : AdicCompletion.QuotientSystem.Presentation I.toIdeal G where
  /-- The homogeneous pieces of the realizing module. -/
  grading : ℤ → Submodule ℤ object
  /-- The realizing grading is an internal direct-sum decomposition. -/
  [decomposition : DirectSum.Decomposition grading]
  /-- The realizing module action respects the grading. -/
  [gradedSMul : SetLike.GradedSMul 𝒜 grading]
  /-- The realizing module is finite over `A`. -/
  [finite : Module.Finite A object]
  /-- The quotient-stage equivalences identify the homogeneous pieces exactly. -/
  quotientEquiv_mem_iff :
    ∀ (n : ℕ+) (d : ℤ)
      (x : object ⧸ I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A object)),
      equiv n x ∈ 𝒢 n d ↔
        x ∈
          (grading d).map
            ((Submodule.mkQ
              (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A object))).restrictScalars ℤ)

namespace Realization

attribute [instance] Realization.decomposition Realization.gradedSMul Realization.finite

/-- Build a graded realization from an explicit quotient-system presentation,
grading, and homogeneous-piece compatibility. -/
@[stacks 0EKC "graded realization constructor"]
def of
    {I : HomogeneousIdeal 𝒜}
    {G : PNatInverseSystem (ModuleCat.{v} A)}
    {𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G.stage n)}
    (P : AdicCompletion.QuotientSystem.Presentation I.toIdeal G)
    (grading : ℤ → Submodule ℤ P.object)
    [DirectSum.Decomposition grading]
    [SetLike.GradedSMul 𝒜 grading]
    [Module.Finite A P.object]
    (quotientEquiv_mem_iff :
      ∀ (n : ℕ+) (d : ℤ)
        (x : P.object ⧸ I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A P.object)),
        P.equiv n x ∈ 𝒢 n d ↔
          x ∈
            (grading d).map
              ((Submodule.mkQ
                (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A P.object))).restrictScalars ℤ)) :
    Realization 𝒜 I G 𝒢 where
  toPresentation := P
  grading := grading
  decomposition := inferInstance
  gradedSMul := inferInstance
  finite := inferInstance
  quotientEquiv_mem_iff := quotientEquiv_mem_iff

/-- Lemma 10.98.3 (0EKC): a positive inverse system of finite graded modules
with the stated successor kernel condition admits a finite graded adic
quotient realization. -/
@[stacks 0EKC]
theorem nonempty
    [IsNoetherianRing A]
    (I : HomogeneousIdeal 𝒜)
    (h_irrelevant : I ≤ 𝒜₊)
    (G : PNatInverseSystem (ModuleCat.{max u v} A))
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G.stage n))
    [∀ n : ℕ+, DirectSum.Decomposition (𝒢 n)]
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    [∀ n : ℕ+, Module.Finite A (G.stage n)]
    (h_transition_degree :
      ∀ (n : ℕ+) (d : ℤ) {x : G.stage (n + 1)},
        x ∈ 𝒢 (n + 1) d → G.stepLinearMap n x ∈ 𝒢 n d)
    (h_step_surjective : ∀ n : ℕ+, Function.Surjective (G.stepLinearMap n))
    (h_step_kernel :
      ∀ n : ℕ+,
        LinearMap.ker (G.stepLinearMap n) =
          I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G.stage (n + 1)))) :
    Nonempty (Realization 𝒜 I G 𝒢) := sorry

end Realization

/-- Lemma 10.98.4 (0EKD): if the tensor-to-limit completion comparison of a
degree-preserving positive inverse-system cone is an isomorphism, then so is
the induced map on every homogeneous degree. -/
@[stacks 0EKD]
theorem degreewiseLimitMap_isIso
    (I : HomogeneousIdeal 𝒜)
    (h_irrelevant : I ≤ 𝒜₊)
    (G : PNatInverseSystem (ModuleCat.{max u v} A))
    (s : Cone G)
    (𝓜 : ℤ → Submodule ℤ s.pt)
    [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝒜 𝓜]
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G.stage n))
    [∀ n : ℕ+, DirectSum.Decomposition (𝒢 n)]
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h_transition_degree :
      ∀ {i j : ℕ+} (hij : i ≤ j) (d : ℤ) {x : G.stage j},
        x ∈ 𝒢 j d → G.transitionLinearMap hij x ∈ 𝒢 i d)
    (h_stage_annihilated :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G.stage n)) = ⊥)
    (h_cone_degree :
      ∀ (n : ℕ+) (d : ℤ) {x : s.pt},
        x ∈ 𝓜 d → PNatInverseSystem.Cone.stageMap s n x ∈ 𝒢 n d)
    [IsIso (PNatInverseSystem.Cone.tensorToLimitOfAnnihilated
      s I.toIdeal h_stage_annihilated)]
    (d : ℤ) :
    IsIso (GradedModule.PNat.limitMap 𝒜 G s 𝓜 𝒢 h_transition_degree h_cone_degree d) := sorry

end AdicCompletion.Graded
