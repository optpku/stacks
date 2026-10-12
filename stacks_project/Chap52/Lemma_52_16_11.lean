/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.PrincipalFiniteLocalCohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Lemma 52.16.11 (1): a principal regular ideal with finite locally free stages
and finite first and second local cohomology canonically extends a coherent formal
module to `S.X`. -/
@[stacks 0DXW] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.canonicallyExtends_of_principal_finiteLocalCohomology :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A)
      (F : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
      (f : A)
      (h_I : S.I = Ideal.span ({f} : Set A))
      (h_f_mem : f ∈ S.a)
      (h_f_regular : IsRegular f)
      (h_stage : ∀ n : ℕ, IsFiniteLocallyFreeStage F n)
      [Module.Finite A
        ((localCohomology S.a 1).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A)))))]
      [Module.Finite A
        ((localCohomology S.a 2).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A)))))]
      , CanonicallyExtends S F)

/- Lemma 52.16.11 (2): under the same principal, regularity, stage, and local
cohomology hypotheses, if `A` is `S.I`-adically complete then `F` is in the
essential image of the coherent completion functor on `S.U`. -/
@[stacks 0DXW] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.isCompletion_of_principal_finiteLocalCohomology :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A) [IsAdicComplete S.I A]
      (F : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
      (f : A)
      (h_I : S.I = Ideal.span ({f} : Set A))
      (h_f_mem : f ∈ S.a)
      (h_f_regular : IsRegular f)
      (h_stage : ∀ n : ℕ, IsFiniteLocallyFreeStage F n)
      [Module.Finite A
        ((localCohomology S.a 1).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A)))))]
      [Module.Finite A
        ((localCohomology S.a 2).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A)))))]
      , (CoherentCompletion.functor
          ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F)

end AlgebraicGeometry.Scheme.CoherentFormalModules
