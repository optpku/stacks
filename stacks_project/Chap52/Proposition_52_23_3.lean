module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.FlatLocalBase
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Proposition 52.23.3 (1) -/
@[stacks 0EJU] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.canonicallyExtends_of_flatOverLocalBase :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {R : Type v} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
      (S : AffineAlgebraizationSetup A)
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
          (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 1))),
      CanonicallyExtends S F)

/- Proposition 52.23.3 (2) -/
@[stacks 0EJU] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.isCompletion_of_flatOverLocalBase :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {R : Type v} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
      (S : AffineAlgebraizationSetup A) [IsAdicComplete S.I A]
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
          (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 1))),
      (CoherentCompletion.functor
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F)

end AlgebraicGeometry.Scheme.CoherentFormalModules
