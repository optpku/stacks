/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.RegularSequence
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Proposition 52.23.1 (1) -/
@[stacks 0EJS] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.canonicallyExtends_of_regularSequence :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A)
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
          (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 1))),
      CanonicallyExtends S F)

/- Proposition 52.23.1 (2) -/
@[stacks 0EJS] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.isCompletion_of_regularSequence :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A) [IsAdicComplete S.I A]
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
          (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 1))),
      (CoherentCompletion.functor
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F)

end AlgebraicGeometry.Scheme.CoherentFormalModules
