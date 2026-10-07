module

import stacks_project.Chap30.Proposition_30_25_4
import stacks_project.Chap30.Theorem_30_27_1_Grothendieck_s_existence_theorem

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

/-- Remark 30.27.2 (Unwinding Grothendieck's existence theorem) (1): if `A` is Noetherian and
`I`-adically complete and `f : X ⟶ Spec(A)` is separated of finite type, then completion is an
equivalence from coherent `𝒪_X`-modules with support proper over `A` to coherent formal `I 𝒪_X`-modules
with first-stage support proper over `Spec(A)`. -/
@[stacks 088F, instance]
instance coherentProperSupportCompletionFunctor_isEquivalence
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsNoetherian X]
    (I : Ideal A) [IsAdicComplete I A] (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [Scheme.Hom.FiniteType f] :
    (coherentProperSupportCompletionFunctor :
      CoherentProperSupportOver f ⥤
        CoherentFormalProperSupportOver f ((idealSheafDataOfIdealOnSpec I).comap f)).IsEquivalence :=
  sorry

/-- Remark 30.27.2 (Unwinding Grothendieck's existence theorem) (2): if `X` is proper over `A`, the
unrestricted coherent-completion functor `Coh(𝒪_X) ⥤ Coh(X, I 𝒪_X)` is an equivalence, so the
support conditions may be omitted. -/
@[stacks 088F, instance]
instance coherentCompletionFunctor_isEquivalence_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsNoetherian X]
    (I : Ideal A) [IsAdicComplete I A] (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] :
    (CoherentCompletion.functor ((idealSheafDataOfIdealOnSpec I).comap f)).IsEquivalence :=
  sorry

