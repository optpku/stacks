/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.CanonicalExtension
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
public import ReasLib.RingTheory.AdicCompletion.CompleteModule
public import ReasLib.RingTheory.Topology.Adic.InverseLimit

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- A canonically extending coherent formal module has a coherent realization on `S.X`,
unique up to the unique isomorphism compatible with its pro-realization. -/
theorem canonicallyExtends_existsUnique (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_extends : CanonicallyExtends S F) :
    ∃ G : CoherentFormalModules S.X (Scheme.idealSheafDataOfIdealOnSpec S.I),
      ∃ e : (proFunctor (Scheme.idealSheafDataOfIdealOnSpec S.I)).obj G ≅
          sectionsProObject S F,
        ∀ (G' : CoherentFormalModules S.X
            (Scheme.idealSheafDataOfIdealOnSpec S.I))
          (e' : (proFunctor (Scheme.idealSheafDataOfIdealOnSpec S.I)).obj G' ≅
            sectionsProObject S F),
          ∃! i : G ≅ G',
            (proFunctor (Scheme.idealSheafDataOfIdealOnSpec S.I)).mapIso i ≪≫ e' = e := sorry

/-- Every coherent formal module on `S.X` realizing the global-section pro-object
restricts to the original coherent formal module on `S.U`. -/
theorem canonicallyExtends_restriction (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_extends : CanonicallyExtends S F)
    (G : CoherentFormalModules S.X (Scheme.idealSheafDataOfIdealOnSpec S.I)) :
    Nonempty ((proFunctor (Scheme.idealSheafDataOfIdealOnSpec S.I)).obj G ≅
      sectionsProObject S F) →
    Nonempty
      ((Scheme.coherentFormalModulesRestrictionFunctor
          (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U).obj G ≅ F) := sorry

/-- A canonically extending coherent formal module belongs to the essential image of
restriction from `S.X` to `S.U`. -/
theorem canonicallyExtends_extends (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) :
    CanonicallyExtends S F →
      (Scheme.coherentFormalModulesRestrictionFunctor
        (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U).essImage F := sorry

/-- The global-section inverse system of a canonically extending coherent formal module
satisfies the Mittag-Leffler condition. -/
theorem canonicallyExtends_isMittagLeffler (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_extends : CanonicallyExtends S F) :
    IsMittagLeffler (sectionsSystem S F) := sorry

/-- The inverse limit of global sections of a canonically extending coherent formal module
is complete for the `S.I`-adic topology. -/
theorem sectionsLimit_isAdicComplete_of_canonicallyExtends
    (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) :
    CanonicallyExtends S F → IsAdicComplete S.I (sectionsLimit S F) := sorry

/-- The inverse limit of global sections, equipped with its canonical module structure over
the `S.I`-adic completion of `A`. -/
noncomputable def sectionsLimitCompletedModule (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_complete : IsAdicComplete S.I (sectionsLimit S F)) :
    ModuleCat (AdicCompletion S.I A) :=
  @ModuleCat.of (AdicCompletion S.I A) _ (sectionsLimit S F) _
    (@IsAdicComplete.completedModule A _ S.I (sectionsLimit S F) _ _
      h_complete)

/-- Restricting the completed-ring action on the inverse-limit module to `A` recovers
the original inverse-limit module. -/
theorem sectionsLimitCompletedModule_restrictScalars
    (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_complete : IsAdicComplete S.I (sectionsLimit S F)) :
    (ModuleCat.restrictScalars (algebraMap A (AdicCompletion S.I A))).obj
        (sectionsLimitCompletedModule S F h_complete) =
      ModuleCat.of A (sectionsLimit S F) := sorry

/-- The inverse-limit module of a canonically extending coherent formal module is finite
over the `S.I`-adic completion of `A`. -/
theorem canonicallyExtends_sectionsLimit_finite (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_extends : CanonicallyExtends S F) :
    Module.Finite (AdicCompletion S.I A)
      (sectionsLimitCompletedModule S F
        (sectionsLimit_isAdicComplete_of_canonicallyExtends S F h_extends)) := sorry

/-- The inverse-limit topology on global sections of a canonically extending coherent formal
module is the `S.I`-adic topology. -/
theorem canonicallyExtends_limitTopology_eq_adic (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_extends : CanonicallyExtends S F) :
    Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
