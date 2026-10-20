module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Completion.Proper
public import Mathlib.CategoryTheory.EssentialImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

universe u

/- Remark 76.42.12 (Unwinding Grothendieck's existence theorem) (1): completion
over an I-adically complete Noetherian ring A is an equivalence from coherent
𝒪_X-modules with support proper over Spec A to compatible coherent systems on
X_n = X ×_{Spec A} Spec(A/I^n) whose first stage has support proper over Spec(A/I).
Here X is separated and of finite type over Spec A. Canonical formal systems
represent the sheaves on X_n by coherent modules on X annihilated by I^n,
with induced successor quotient isomorphisms F_{n+1}/I^n F_{n+1} ≅ F_n.
Stage zero is forced to vanish. The first-stage support factors through
Spec(A/I), so its properness over Spec A is equivalent to properness over
Spec(A/I). -/
@[stacks 08BF] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.instIsEquivalence_coherentProperSupportCompletionFunctor :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [FiniteType (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase X)],
      (coherentProperSupportCompletionFunctor (SchemeRealization.toBase X)
        (pullbackIdeal I (SchemeRealization.toBase X))).IsEquivalence)

/- Remark 76.42.12 (Unwinding Grothendieck's existence theorem) (2): if X is
proper over Spec A, unrestricted coherent completion is an equivalence, so
both support conditions may be omitted. -/
@[stacks 08BF] #check
  (AlgebraicGeometry.AlgebraicSpace.CoherentCompletion.functor_isEquivalence_of_isProper :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))} [Proper (SchemeRealization.toBase X)],
      (CoherentCompletion.functor (pullbackIdeal I (SchemeRealization.toBase X))).IsEquivalence)

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A) [IsAdicComplete I A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))} [Proper (SchemeRealization.toBase X)]

/- Every coherent formal module lies in the essential image of unrestricted
completion when X is proper over the complete Noetherian base. -/
#check
  (CategoryTheory.Functor.EssSurj.mem_essImage
    (CoherentCompletion.functor (pullbackIdeal I (SchemeRealization.toBase X))) :
    ∀ F : CoherentFormalModules X (pullbackIdeal I (SchemeRealization.toBase X)),
      (CoherentCompletion.functor (pullbackIdeal I (SchemeRealization.toBase X))).essImage F)

end
