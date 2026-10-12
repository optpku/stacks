/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Theorem_76_42_11_Grothendieck_s_existence_theorem
public import stacks_project.Chap76.«76_42_2_1_Completion»
public import stacks_project.Chap76.Lemma_76_42_6_Hom
public import stacks_project.Chap67.Definition_67_40_1_Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

noncomputable section

universe u

/- Remark 76.42.12 (Unwinding Grothendieck's existence theorem) (1): in Situation
76.42.5, Theorem 76.42.11 says completion is an equivalence from coherent
𝒪_X-modules with support proper over A to systems (ℱ_n, φ_n) of coherent
𝒪_{X_n}-modules with i_n^* ℱ_{n+1} ≅ ℱ_n and Supp(ℱ_1) proper over S_1,
identified with CoherentFormalProperSupportOver (toBase X)
(pullbackIdeal I (toBase X)). -/
@[stacks 08BF] #check instIsEquivalence_coherentProperSupportCompletionFunctor

namespace AlgebraicGeometry.AlgebraicSpace.CoherentCompletion

/-- Remark 76.42.12 (Unwinding Grothendieck's existence theorem) (2): if `X` is
proper over `A`, the unrestricted coherent-completion functor
`functor (pullbackIdeal I (toBase X))` is an equivalence, so the support
conditions may be omitted. -/
@[stacks 08BF, instance]
instance functor_isEquivalence_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} [Proper (toBase X)] :
    (functor (pullbackIdeal I (toBase X))).IsEquivalence :=
  sorry

/-- Every coherent formal module along `I 𝒪_X` lies in the essential image of
coherent completion when `toBase X` is proper over an `I`-adically complete
Noetherian ring. -/
theorem mem_essImage_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} [Proper (toBase X)]
    (F : CoherentFormalModules X (pullbackIdeal I (toBase X))) :
    (functor (pullbackIdeal I (toBase X))).essImage F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentCompletion
