module

public import Mathlib.RingTheory.Regular.RegularSequence
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Local
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.CanonicalExtension
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/--
If a finite family in an ideal generates its extensions on the relevant open
stalks and is regular on the completed stalks, finite degree-zero and
degree-one cohomology imply canonical extension of the coherent formal module.
-/
theorem canonicallyExtends_of_regularSequence (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (d : ℕ) (f : Fin d → A) (h_mem : ∀ i, f i ∈ S.I)
    (h_generate : ∀ y : S.Y, (hy : S.y y ∈ S.U) →
      let yU := closedFiberOpenPoint S y hy
      S.I.map (ambientLocalRingMap S yU) =
        Ideal.span (Set.range (fun i ↦ ambientLocalRingMap S yU (f i))))
    (h_regular : ∀ y : S.Y, (hy : S.y y ∈ S.U) →
      let yU := closedFiberOpenPoint S y hy
      RingTheory.Sequence.IsRegular (completedStalk S F yU)
        (List.ofFn (fun i ↦
          ((algebraMap ((S.U.toScheme).presheaf.stalk yU) (completedLocalRing S yU)).comp
            (localRingMap S yU)) (f i))))
    (h_finite_zero : Module.Finite A
      ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
        (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 0)))
    (h_finite_one : Module.Finite A
      ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
        (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 1))) :
    CanonicallyExtends S F := sorry

/--
If the coefficient ring is adically complete, the regular-sequence criterion
also identifies the coherent formal module with the completion of a coherent
module on the relevant open subscheme.
-/
theorem isCompletion_of_regularSequence (S : AffineAlgebraizationSetup A)
    [IsAdicComplete S.I A]
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (d : ℕ) (f : Fin d → A) (h_mem : ∀ i, f i ∈ S.I)
    (h_generate : ∀ y : S.Y, (hy : S.y y ∈ S.U) →
      let yU := closedFiberOpenPoint S y hy
      S.I.map (ambientLocalRingMap S yU) =
        Ideal.span (Set.range (fun i ↦ ambientLocalRingMap S yU (f i))))
    (h_regular : ∀ y : S.Y, (hy : S.y y ∈ S.U) →
      let yU := closedFiberOpenPoint S y hy
      RingTheory.Sequence.IsRegular (completedStalk S F yU)
        (List.ofFn (fun i ↦
          ((algebraMap ((S.U.toScheme).presheaf.stalk yU) (completedLocalRing S yU)).comp
            (localRingMap S yU)) (f i))))
    (h_finite_zero : Module.Finite A
      ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
        (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 0)))
    (h_finite_one : Module.Finite A
      ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
        (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 1))) :
    (CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
