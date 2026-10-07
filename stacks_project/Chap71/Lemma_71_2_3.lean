module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Lemma_67_15_1_ModuleSupport
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated

/-!
# Lemma 71.2.3

The weakly associated locus of a quasi-coherent module on an algebraic space is
contained in the support of that module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Lemma 71.2.3: for a scheme `S`, an algebraic space `X` over `S`, and a
quasi-coherent `𝒪_X`-module `F`, the weakly associated locus of `F` is contained
in the support of `F`. -/
@[stacks 0CTY]
theorem weakAss_subset_support (F : X.Modules) [F.IsQuasicoherent] :
    F.weakAss ⊆ F.moduleSupport :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
