module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.MapAnnihilation

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- A morphism of coherent formal modules on `S.U` whose stagewise kernel and
cokernel are uniformly annihilated by a power of `S.I` preserves extendability
to `S.X` in both directions. -/
theorem extends_iff_of_powerTorsionKernelCokernel (S : AffineAlgebraizationSetup A)
    {F F' : Scheme.CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)} (f : F ⟶ F')
    (hf : Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) f) :
    (Scheme.coherentFormalModulesRestrictionFunctor
      (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U).essImage F ↔
        (Scheme.coherentFormalModulesRestrictionFunctor
          (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U).essImage F' := sorry

/-- A morphism of coherent formal modules on `S.U` whose stagewise kernel and
cokernel are uniformly annihilated by a power of `S.I` preserves membership in
the essential image of coherent completion in both directions. -/
theorem completion_iff_of_powerTorsionKernelCokernel (S : AffineAlgebraizationSetup A)
    {F F' : Scheme.CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)} (f : F ⟶ F')
    (hf : Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) f) :
    (Scheme.CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F ↔
        (Scheme.CoherentCompletion.functor
          ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F' := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
