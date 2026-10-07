module

public import ReasLib.RingTheory.LocalCohomology.PrincipalQuotient
public import ReasLib.AlgebraicGeometry.Scheme.LocalCohomology.Serre
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped ENat

noncomputable section

universe u

namespace Module.LocalCohomology

/- Remark 52.16.12 (1): under universal catenarity and Cohen--Macaulay formal
fibers, finiteness of the first two local-cohomology modules of `A/fA` is
equivalent to the strict depth-plus-quotient-dimension inequality. -/
@[stacks 0EHI] #check (@Module.LocalCohomology.finite_one_two_iff_depth_add_quotientDim :
    ∀ {A : Type u} [CommRing A] [UniversallyCatenaryRing.{u, u} A]
      (𝔞 : Ideal A) (f : A), f ∈ 𝔞 → IsRegular f →
      (∀ p : PrimeSpectrum A,
        FieldAlgebraProperty.cohenMacaulay.HoldsOnFormalFibers
          (Localization.AtPrime p.asIdeal)) →
      ((Module.Finite A
        ((localCohomology 𝔞 1).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A))))) ∧
      Module.Finite A
        ((localCohomology 𝔞 2).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A)))))) ↔
      ∀ p q : PrimeSpectrum A,
        p ∈ PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) →
          p ∉ PrimeSpectrum.zeroLocus (𝔞 : Set A) →
            q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (𝔞 : Set A) →
              (.some (2 : ℕ∞) : WithBot ℕ∞) <
                (.some (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal
                    (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A))))) :
                  WithBot ℕ∞) +
                  ringKrullDim (p.asIdeal.quotientAtPrime q)))

/- Remark 52.16.12 (2): if the quotient `A/fA` satisfies `(S₂)` and every
irreducible component of `V(𝔞)` has codimension at least three in
`Spec(A/fA)`, then the first two local-cohomology modules are finite. -/
@[stacks 0EHI] #check (@Module.LocalCohomology.finite_one_two_of_s2_codim :
    ∀ {A : Type u} [CommRing A] [UniversallyCatenaryRing.{u, u} A]
      (S : AffineAlgebraizationSetup A) (f : A),
      S.I = Ideal.span ({f} : Set A) → f ∈ S.a → IsRegular f →
      (∀ p : PrimeSpectrum A,
        FieldAlgebraProperty.cohenMacaulay.HoldsOnFormalFibers
          (Localization.AtPrime p.asIdeal)) →
      satisfiesSerreConditionS S.Y 2 →
      (∀ (Y' : irreducibleComponents S.Y) (Z' : irreducibleComponents S.Z)
        (hZY :
          TopologicalSpace.IrreducibleCloseds.map S.z.base S.z.continuous
              (S.Z.irreducibleComponentIrreducibleClosed Z') ≤
            TopologicalSpace.IrreducibleCloseds.map S.y.base S.y.continuous
              (S.Y.irreducibleComponentIrreducibleClosed Y')),
        (3 : ℕ∞) ≤ TopologicalSpace.codimBetween
          (TopologicalSpace.IrreducibleCloseds.map S.z.base S.z.continuous
            (S.Z.irreducibleComponentIrreducibleClosed Z'))
          (TopologicalSpace.IrreducibleCloseds.map S.y.base S.y.continuous
            (S.Y.irreducibleComponentIrreducibleClosed Y')) hZY) →
      Module.Finite A
        ((localCohomology S.a 1).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A))))) ∧
      Module.Finite A
        ((localCohomology S.a 2).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A))))))

end Module.LocalCohomology

end
