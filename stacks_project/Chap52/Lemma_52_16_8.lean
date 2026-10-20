module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.CanonicalExtensionConsequences
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Lemma 52.16.8: a canonically extending coherent formal module has a unique coherent
realization on `S.X`, restricts back to `S.U`, has Mittag-Leffler global sections, and has a
finite inverse-limit module over the adic completion with its adic limit topology. -/
@[stacks 0EIR]
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.canonicallyExtends_existsUnique :
  ∀ (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
    CanonicallyExtends S F →
      ∃ G : CoherentFormalModules S.X (Scheme.idealSheafDataOfIdealOnSpec S.I),
        ∃ e : (proFunctor (Scheme.idealSheafDataOfIdealOnSpec S.I)).obj G ≅
            sectionsProObject S F,
          ∀ (G' : CoherentFormalModules S.X
              (Scheme.idealSheafDataOfIdealOnSpec S.I))
            (e' : (proFunctor (Scheme.idealSheafDataOfIdealOnSpec S.I)).obj G' ≅
              sectionsProObject S F),
            ∃! i : G ≅ G',
              (proFunctor (Scheme.idealSheafDataOfIdealOnSpec S.I)).mapIso i ≪≫ e' = e)

/- Complete source-facing checks for the promoted consequences. -/
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.canonicallyExtends_restriction :
  ∀ (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
    CanonicallyExtends S F →
      ∀ (G : CoherentFormalModules S.X (Scheme.idealSheafDataOfIdealOnSpec S.I)),
        Nonempty ((proFunctor (Scheme.idealSheafDataOfIdealOnSpec S.I)).obj G ≅
          sectionsProObject S F) →
        Nonempty
          ((Scheme.coherentFormalModulesRestrictionFunctor
              (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U).obj G ≅ F))
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.canonicallyExtends_extends :
  ∀ (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
    CanonicallyExtends S F →
      (Scheme.coherentFormalModulesRestrictionFunctor
        (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U).essImage F)
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.canonicallyExtends_isMittagLeffler :
  ∀ (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
    CanonicallyExtends S F → IsMittagLeffler (sectionsSystem S F))
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.sectionsLimit_isAdicComplete_of_canonicallyExtends :
  ∀ (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
    CanonicallyExtends S F → IsAdicComplete S.I (sectionsLimit S F))
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.sectionsLimitCompletedModule :
  ∀ (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_complete : IsAdicComplete S.I (sectionsLimit S F)),
    ModuleCat (AdicCompletion S.I A))
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.sectionsLimitCompletedModule_restrictScalars :
  ∀ (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_complete : IsAdicComplete S.I (sectionsLimit S F)),
    (ModuleCat.restrictScalars (algebraMap A (AdicCompletion S.I A))).obj
        (sectionsLimitCompletedModule S F h_complete) =
      ModuleCat.of A (sectionsLimit S F))
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.canonicallyExtends_sectionsLimit_finite :
  ∀ (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
    ∀ (h_extends : CanonicallyExtends S F),
      Module.Finite (AdicCompletion S.I A)
        (sectionsLimitCompletedModule S F
          (sectionsLimit_isAdicComplete_of_canonicallyExtends S F h_extends)))
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.canonicallyExtends_limitTopology_eq_adic :
  ∀ (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
    CanonicallyExtends S F →
      Functor.limitTopology (sectionsSystem S F) =
        Ideal.adicModuleTopology S.I (sectionsLimit S F))

end AlgebraicGeometry.Scheme.CoherentFormalModules
