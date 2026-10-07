module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.Affine
public import stacks_project.Chap52.Lemma_52_16_3_Instances
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry.Scheme AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

/- Lemma 52.16.3 (1): the five algebraization conditions for a coherent formal
module on `U` are equivalent. -/
@[stacks 0EIL]
#check
  (AlgebraicGeometry.AffineAlgebraizationSetup.algebraization_tfae :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A)
      (F : CoherentFormalModules S.U.toScheme
        ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
      let U := S.U.toScheme
      let IX := idealSheafDataOfIdealOnSpec S.I
      let IU := IX.comap S.U.ι
      let c₁ := (CoherentCompletion.functor IU).essImage F
      let c₂ := ∃ G : Coh U.toRingedSpace,
        Nonempty ((CoherentCompletion.functor IU).obj G ≅ F)
      let c₃ := ∃ V : TopologicalSpace.Opens S.U,
        (IU.support : Set S.U) ⊆ (V : Set S.U) ∧
          (CoherentCompletion.functor (IU.comap (Scheme.Opens.ι V))).essImage
            ((coherentFormalModulesRestrictionFunctor IU V).obj F)
      let c₄ :=
        (Modules.coherentRestrictFunctor S.U.ι ⋙
          CoherentCompletion.functor IU).essImage F
      let c₅ :=
        (CoherentCompletion.functor IX ⋙
          coherentFormalModulesRestrictionFunctor IX S.U).essImage F
      List.TFAE [c₁, c₂, c₃, c₄, c₅])

/- Lemma 52.16.3 (2): completion on `X` followed by restriction to `U`
implies extension to a coherent formal module on `X`. -/
@[stacks 0EIL]
#check
  (AlgebraicGeometry.AffineAlgebraizationSetup.extends_of_globalCompletion :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A)
      (F : CoherentFormalModules S.U.toScheme
        ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
      let IX := idealSheafDataOfIdealOnSpec S.I
      (CoherentCompletion.functor IX ⋙
        coherentFormalModulesRestrictionFunctor IX S.U).essImage F →
          (coherentFormalModulesRestrictionFunctor IX S.U).essImage F)

/- Lemma 52.16.3 (3): if `A` is `S.I`-adically complete, extension to `X`
implies completion on `X` followed by restriction to `U`. -/
@[stacks 0EIL]
#check
  (AlgebraicGeometry.AffineAlgebraizationSetup.globalCompletion_of_extends :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A) [IsAdicComplete S.I A]
      (F : CoherentFormalModules S.U.toScheme
        ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
      let IX := idealSheafDataOfIdealOnSpec S.I
      (coherentFormalModulesRestrictionFunctor IX S.U).essImage F →
        (CoherentCompletion.functor IX ⋙
          coherentFormalModulesRestrictionFunctor IX S.U).essImage F)

end AlgebraicGeometry.AffineAlgebraizationSetup
