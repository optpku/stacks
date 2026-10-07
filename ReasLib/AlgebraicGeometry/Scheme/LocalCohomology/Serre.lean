module

public import ReasLib.RingTheory.LocalCohomology.PrincipalQuotient
public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization
public import ReasLib.AlgebraicGeometry.Scheme.Depth
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped ENat

noncomputable section

universe u

namespace Module.LocalCohomology

/-- Serre condition `(S₂)` together with codimension at least three for the
components of a closed subscheme implies finiteness of the first two
local-cohomology modules of a principal regular quotient. -/
theorem finite_one_two_of_s2_codim
    {A : Type u} [CommRing A] [UniversallyCatenaryRing.{u, u} A]
    (S : AffineAlgebraizationSetup A) (f : A)
    (h_I : S.I = Ideal.span ({f} : Set A)) (h_f_mem : f ∈ S.a)
    (h_f_regular : IsRegular f)
    (h_formal : ∀ p : PrimeSpectrum A,
      FieldAlgebraProperty.cohenMacaulay.HoldsOnFormalFibers
        (Localization.AtPrime p.asIdeal))
    (h_s2 : satisfiesSerreConditionS S.Y 2)
    (h_codim : ∀ (Y' : irreducibleComponents S.Y)
      (Z' : irreducibleComponents S.Z)
      (hZY :
        TopologicalSpace.IrreducibleCloseds.map S.z.base S.z.continuous
            (S.Z.irreducibleComponentIrreducibleClosed Z') ≤
          TopologicalSpace.IrreducibleCloseds.map S.y.base S.y.continuous
            (S.Y.irreducibleComponentIrreducibleClosed Y')),
      (3 : ℕ∞) ≤ TopologicalSpace.codimBetween
        (TopologicalSpace.IrreducibleCloseds.map S.z.base S.z.continuous
          (S.Z.irreducibleComponentIrreducibleClosed Z'))
        (TopologicalSpace.IrreducibleCloseds.map S.y.base S.y.continuous
          (S.Y.irreducibleComponentIrreducibleClosed Y')) hZY) :
    Module.Finite A
        ((localCohomology S.a 1).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A))))) ∧
      Module.Finite A
        ((localCohomology S.a 2).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A))))) := sorry

end Module.LocalCohomology

end
