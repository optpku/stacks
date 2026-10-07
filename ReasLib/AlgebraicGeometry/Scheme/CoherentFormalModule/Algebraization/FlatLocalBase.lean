module

public import ReasLib.Algebra.Module.Flat.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Local
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.CanonicalExtension
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {R : Type v} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A local-base flatness criterion for canonical algebraization of a coherent
formal module, with finite cohomology in degrees zero and one. -/
theorem canonicallyExtends_of_flatOverLocalBase (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (φ : R →+* A)
    (h_ideal : S.I = (IsLocalRing.maximalIdeal R).map φ)
    (h_flat : ∀ y : S.Y, (hy : S.y y ∈ S.U) →
      let yU := closedFiberOpenPoint S y hy
      Module.FlatAlong (((algebraMap _ (completedLocalRing S yU)).comp
        (localRingMap S yU)).comp φ) (completedStalk S F yU))
    (h_finite_zero : Module.Finite A
      ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
        (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 0)))
    (h_finite_one : Module.Finite A
      ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
        (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 1))) :
    CanonicallyExtends S F := sorry

/-- Under adic completeness, the local-base flatness criterion identifies a
coherent formal module with the completion of a coherent module. -/
theorem isCompletion_of_flatOverLocalBase (S : AffineAlgebraizationSetup A)
    [IsAdicComplete S.I A]
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (φ : R →+* A)
    (h_ideal : S.I = (IsLocalRing.maximalIdeal R).map φ)
    (h_flat : ∀ y : S.Y, (hy : S.y y ∈ S.U) →
      let yU := closedFiberOpenPoint S y hy
      Module.FlatAlong (((algebraMap _ (completedLocalRing S yU)).comp
        (localRingMap S yU)).comp φ) (completedStalk S F yU))
    (h_finite_zero : Module.Finite A
      ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
        (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 0)))
    (h_finite_one : Module.Finite A
      ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
        (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 1))) :
    (CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
