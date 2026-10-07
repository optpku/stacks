module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.Graded
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 52.28.4: a canonically extending graded formal module system is induced by one
finite graded module, both modulo irrelevant-ideal power torsion and after completion. -/
@[stacks 0EL4] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.Graded.exists_finite_of_canonicallyExtends :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {𝒜 : ℕ → Submodule ℤ A} [GradedAlgebra 𝒜]
      (S : AffineAlgebraizationSetup A) (I : HomogeneousIdeal 𝒜)
      (h_a : S.a = (HomogeneousIdeal.irrelevant 𝒜).toIdeal) (h_I : S.I = I.toIdeal)
      (F : Scheme.CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
      (M : SequentialInverseSystem (GradedModuleCat 𝒜)),
      AffineAlgebraizationSetup.Graded.Realizes S F M →
      Scheme.CoherentFormalModules.CanonicallyExtends S F →
      ∃ N : GradedModuleCat.FG 𝒜,
        Nonempty
          (GradedModuleCat.torsionQuotientPro (HomogeneousIdeal.irrelevant 𝒜).toIdeal
              (AdicCompletion.Graded.idealPowerQuotientSystem I N.obj) ≅
            GradedModuleCat.torsionQuotientPro (HomogeneousIdeal.irrelevant 𝒜).toIdeal M) ∧
        Nonempty
          ((Scheme.coherentFormalModulesRestrictionFunctor
              (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U).obj
              ((Scheme.CoherentCompletion.functor (Scheme.idealSheafDataOfIdealOnSpec S.I)).obj
                (AffineAlgebraizationSetup.Graded.associatedCoherent S N)) ≅ F))
