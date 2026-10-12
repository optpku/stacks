/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import stacks_project.Chap76.Lemma_76_42_6_Hom
public import stacks_project.Chap76.«76_42_5_1_ProperSupport»

/-!
# Full and faithful instances for proper-support completion

In Situation 76.42.5, the restricted completion functor from coherent modules
with support proper over `Spec A` is full and faithful.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- In Situation 76.42.5, the restricted completion functor 76.42.5.1 is full. -/
instance instFull_coherentProperSupportCompletionFunctor
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [FiniteType (toBase X)] [Separated (toBase X)] :
    (coherentProperSupportCompletionFunctor (toBase X) (pullbackIdeal I (toBase X))).Full :=
  sorry

/-- In Situation 76.42.5, the restricted completion functor 76.42.5.1 is faithful. -/
instance instFaithful_coherentProperSupportCompletionFunctor
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [FiniteType (toBase X)] [Separated (toBase X)] :
    (coherentProperSupportCompletionFunctor (toBase X) (pullbackIdeal I (toBase X))).Faithful :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
