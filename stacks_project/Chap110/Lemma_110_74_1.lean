module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap108.Lemma_108_4_8_Algebraic
public import stacks_project.Chap110.Lemma_110_74_1_Quot

/-!
# Counterexamples to algebraization of coherent sheaves

Without separatedness of `X ⟶ Spec(A)`, Grothendieck existence, algebraicity of
`Coh_{X/B}`, and algebraicity of `Quot_{𝒪_X/X/B}` all fail for the doubled
finite-type example of this section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.NonseparatedAlgebraization

/-- The structure sheaf of `spaceX k`, as a quasi-coherent module. -/
abbrev structureModule (k : Type u) [Field k] : (spaceX k).Modules :=
  SheafOfModules.unit (structureSheaf (spaceX k))

/-- Unfolding of `structureModule`. -/
theorem structureModule_eq (k : Type u) [Field k] :
    structureModule k = SheafOfModules.unit (structureSheaf (spaceX k)) := sorry

/-- The structure sheaf of `spaceX k` is quasi-coherent. -/
instance instIsQuasicoherent_structureModule (k : Type u) [Field k] :
    (structureModule k).IsQuasicoherent :=
  sorry

/-- Lemma 110.74.1 (1): Grothendieck's existence theorem as stated in Cohomology of Schemes,
Theorem 30.27.1 is false if we drop the assumption that `toSpec k : scheme k ⟶ Spec(A)` is
separated. -/
@[stacks 0ARF]
theorem not_isEquivalence_coherentProperSupportCompletionFunctor {k : Type u} [Field k] :
    ¬ (coherentProperSupportCompletionFunctor :
          CoherentProperSupportOver (toSpec k) ⥤
            CoherentFormalProperSupportOver (toSpec k) (idealSheaf k)).IsEquivalence :=
  sorry

/-- Lemma 110.74.1 (2): the stack of coherent sheaves `Coh_{X/B}` of Quot, Theorems 99.6.1 and
99.5.12, is in general not algebraic if we drop the assumption that `X ⟶ S` is separated. -/
@[stacks 0ARF]
theorem not_isAlgebraicStack {k : Type u} [Field k] :
    ¬ CohStack.AlgebraicStack (CohStack.toGroupoids (spaceHom k)) := sorry

/-- Lemma 110.74.1 (3): the functor `Quot_{𝒪_X/X/B}` of Quot, Proposition 99.8.4 is not an
algebraic space in general if we drop the assumption that `X ⟶ B` is separated. -/
@[stacks 0ARF]
theorem not_isAlgebraicSpaceOver_quot {k : Type u} [Field k] :
    ¬ IsAlgebraicSpaceOver (quot (spaceHom k) (structureModule k)) := sorry

end AlgebraicGeometry.NonseparatedAlgebraization
