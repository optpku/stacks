/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_42_8_FormalModules

/-!
# Ideal-power torsion of kernels and cokernels

This file records sheaf-level annihilation of kernels and cokernels by a power
of an ideal sheaf, both for a single module morphism and uniformly across the
positive stages of a morphism of coherent formal modules.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A morphism of `𝒪_X`-modules has kernel and cokernel annihilated by a
positive power of an ideal sheaf. -/
def HasIdealPowerTorsionKernelCokernel (I : IdealSubobject X) {F G : X.Modules}
    (f : F ⟶ G) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧
    IsAnnihilatedByIdealPower I (kernel f) t ∧
      IsAnnihilatedByIdealPower I (cokernel f) t

/-- Kernel-and-cokernel ideal-power torsion is the existence of a positive power
annihilating both the kernel and the cokernel. -/
theorem hasIdealPowerTorsionKernelCokernel_iff (I : IdealSubobject X)
    {F G : X.Modules} (f : F ⟶ G) :
    HasIdealPowerTorsionKernelCokernel I f ↔
      ∃ t : ℕ, 1 ≤ t ∧
        IsAnnihilatedByIdealPower I (kernel f) t ∧
          IsAnnihilatedByIdealPower I (cokernel f) t :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.CoherentFormalMap

/-- One positive power of an ideal sheaf annihilates the kernels and cokernels
of every positive stage of a morphism of coherent formal modules. -/
def StagesHaveUniformKernelCokernelAnnihilation
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    (K : IdealSubobject X) {E F : CoherentFormalModules X I}
    (alpha : E ⟶ F) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ+,
    Modules.IsAnnihilatedByIdealPower K
        (kernel ((Coh.inclusion X).map (alpha.hom.app (op (n : ℕ))))) t ∧
      Modules.IsAnnihilatedByIdealPower K
        (cokernel ((Coh.inclusion X).map (alpha.hom.app (op (n : ℕ))))) t

/-- Unfold uniform kernel-and-cokernel annihilation across all positive
stages. -/
theorem stagesHaveUniformKernelCokernelAnnihilation_iff
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    (K : IdealSubobject X) {E F : CoherentFormalModules X I}
    (alpha : E ⟶ F) :
    StagesHaveUniformKernelCokernelAnnihilation K alpha ↔
      ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ+,
        Modules.IsAnnihilatedByIdealPower K
            (kernel ((Coh.inclusion X).map (alpha.hom.app (op (n : ℕ))))) t ∧
          Modules.IsAnnihilatedByIdealPower K
            (cokernel ((Coh.inclusion X).map (alpha.hom.app (op (n : ℕ))))) t :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace.CoherentFormalMap
