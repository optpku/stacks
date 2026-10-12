/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EssentialImage
public import stacks_project.Chap76.Lemma_76_42_6_Hom
public import stacks_project.Chap76.«76_42_5_1_ProperSupport»

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A) [IsAdicComplete I A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}
variable [FiniteType (toBase X)] [Separated (toBase X)]

/-- Theorem 76.42.11 (Grothendieck's existence theorem): in Situation 76.42.5,
the restricted completion functor 76.42.5.1 from coherent 𝒪_X-modules with
support proper over Spec A to coherent formal I 𝒪_X-modules whose first stage
has support proper over Spec A is an equivalence of categories. -/
@[stacks 08BE, instance]
instance instIsEquivalence_coherentProperSupportCompletionFunctor :
    (coherentProperSupportCompletionFunctor (toBase X) (pullbackIdeal I (toBase X))).IsEquivalence :=
  sorry

/-- Every coherent formal module along I 𝒪_X whose first stage has support
proper over Spec A lies in the essential image of restricted completion. -/
theorem mem_essImage_coherentProperSupportCompletionFunctor
    (F : CoherentFormalProperSupportOver (toBase X) (pullbackIdeal I (toBase X))) :
    (coherentProperSupportCompletionFunctor (toBase X) (pullbackIdeal I (toBase X))).essImage F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
