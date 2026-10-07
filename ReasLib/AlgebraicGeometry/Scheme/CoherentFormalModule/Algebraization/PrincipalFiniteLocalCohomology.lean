module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.FiniteLocallyFreeStage
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.FiniteSectionImages
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Regular.Defs

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- A principal regular ideal with finite locally free stages and finite first and
second local cohomology yields a canonical extension of a coherent formal module. -/
theorem canonicallyExtends_of_principal_finiteLocalCohomology
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
          (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A)))))] :
    CanonicallyExtends S F := sorry

/-- A principal regular ideal with finite locally free stages and finite first and
second local cohomology yields a coherent completion when the ideal is adically complete. -/
theorem isCompletion_of_principal_finiteLocalCohomology
    (S : AffineAlgebraizationSetup A)
    [IsAdicComplete S.I A]
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
          (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A)))))] :
    (CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
