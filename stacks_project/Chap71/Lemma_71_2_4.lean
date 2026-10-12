/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated

/-!
# Lemma 71.2.4

In a short exact sequence of quasi-coherent modules on an algebraic space, the
weakly associated locus of the middle term is contained in the union of the
outer loci, and the left locus is contained in the middle locus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {C : ShortComplex X.Modules}

/-- Lemma 71.2.4 (1): for a scheme `S`, an algebraic space `X` over `S`, and a
short exact sequence of quasi-coherent `𝒪_X`-modules, every weakly associated
point of the middle term is weakly associated to the left or right term. -/
@[stacks 0CTZ]
theorem weakAss_middle_subset_union_of_shortExact_of_isQuasicoherent
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
    (hC : C.ShortExact) :
    C.X₂.weakAss ⊆ C.X₁.weakAss ∪ C.X₃.weakAss :=
  sorry

/-- Lemma 71.2.4 (2): for a scheme `S`, an algebraic space `X` over `S`, and a
short exact sequence of quasi-coherent `𝒪_X`-modules, every weakly associated
point of the left term is weakly associated to the middle term. -/
@[stacks 0CTZ]
theorem weakAss_left_subset_of_shortExact_of_isQuasicoherent
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
    (hC : C.ShortExact) :
    C.X₁.weakAss ⊆ C.X₂.weakAss :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
