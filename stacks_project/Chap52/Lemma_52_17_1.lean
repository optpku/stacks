module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.PowerTorsion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Lemma 52.17.1 (1): if a morphism of coherent formal modules on `S.U` has
stagewise kernel and cokernel uniformly annihilated by a power of `S.I`, then its
source extends to `S.X` if and only if its target does. -/
@[stacks 0EIU] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.extends_iff_of_powerTorsionKernelCokernel :
    ∀ (S : AffineAlgebraizationSetup A)
    {F F' : Scheme.CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)} (f : F ⟶ F')
    (hf : Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) f),
    (Scheme.coherentFormalModulesRestrictionFunctor
      (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U).essImage F ↔
        (Scheme.coherentFormalModulesRestrictionFunctor
          (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U).essImage F')

/- Lemma 52.17.1 (2): under the same ideal-power kernel-and-cokernel hypothesis,
the source coherent formal module on `S.U` is the completion of a coherent
`𝒪_{S.U}`-module if and only if the target is. -/
@[stacks 0EIU] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.completion_iff_of_powerTorsionKernelCokernel :
    ∀ (S : AffineAlgebraizationSetup A)
    {F F' : Scheme.CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)} (f : F ⟶ F')
    (hf : Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) f),
    (Scheme.CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F ↔
        (Scheme.CoherentCompletion.functor
          ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F')

end AlgebraicGeometry.AffineAlgebraizationSetup
