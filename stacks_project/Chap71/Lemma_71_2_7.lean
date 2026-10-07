module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Lemma_67_15_1_ModuleSupport
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated
public import stacks_project.Chap71.Lemma_71_2_7_MinimalSpecialization

/-!
# Lemma 71.2.7

On a decent algebraic space, every minimal specialization point of the support
of a quasi-coherent module is weakly associated to that module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Lemma 71.2.7: for a scheme `S`, a decent algebraic space `X` over `S`
(for example a quasi-separated or locally separated algebraic space), and a
quasi-coherent `𝒪_X`-module `F`, every minimal specialization point of
`F.moduleSupport` is weakly associated to `F`. -/
@[stacks 0CUM]
theorem minimalSpecializationPoints_support_subset_weakAss
    (F : X.Modules) [F.IsQuasicoherent] [IsDecent X] :
    X.minimalSpecializationPoints F.moduleSupport ⊆ F.weakAss :=
  sorry

/-- If `x` lies in the support of a quasi-coherent module `F` on a decent
algebraic space and no distinct point of that support specializes to `x`, then
`x` is weakly associated to `F`. -/
theorem mem_weakAss_of_mem_moduleSupport_of_eq_of_specializes
    (F : X.Modules) [F.IsQuasicoherent] [IsDecent X] {x : Points X}
    (hx : x ∈ F.moduleSupport)
    (hmin : ∀ ⦃y : Points X⦄, y ∈ F.moduleSupport → Specializes y x → y = x) :
    x ∈ F.weakAss :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
