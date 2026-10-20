module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Completion.Existence
public import stacks_project.Chap76.Lemma_76_42_6_Hom
public import stacks_project.Chap76.«76_42_5_1_ProperSupport»
import StacksCheckRecall

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
variable [FiniteType (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase X)]

/- Theorem 76.42.11 (Grothendieck's existence theorem): in Situation 76.42.5,
the restricted completion functor 76.42.5.1 from coherent 𝒪_X-modules with
support proper over Spec A to coherent formal I 𝒪_X-modules whose first stage
has support proper over Spec A is an equivalence of categories. -/
@[stacks 08BE] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.instIsEquivalence_coherentProperSupportCompletionFunctor :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [FiniteType (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase X)],
      (coherentProperSupportCompletionFunctor (SchemeRealization.toBase X)
        (pullbackIdeal I (SchemeRealization.toBase X))).IsEquivalence)

/- Every coherent formal module along I 𝒪_X whose first stage has support
proper over Spec A lies in the essential image of restricted completion. -/
#check
  (CategoryTheory.Functor.EssSurj.mem_essImage
    (coherentProperSupportCompletionFunctor (SchemeRealization.toBase X)
      (pullbackIdeal I (SchemeRealization.toBase X))) :
    ∀ F : CoherentFormalProperSupportOver (SchemeRealization.toBase X)
      (pullbackIdeal I (SchemeRealization.toBase X)),
      (coherentProperSupportCompletionFunctor (SchemeRealization.toBase X)
        (pullbackIdeal I (SchemeRealization.toBase X))).essImage F)

end AlgebraicGeometry.AlgebraicSpace.Modules
