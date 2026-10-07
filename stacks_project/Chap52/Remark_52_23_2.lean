module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.FinitenessCriterion
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Remark 52.23.2 (1) -/
@[stacks 0EJT] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.firstStageCohomology_finite_iff_depth_add_pointClosureDim :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
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
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H),
    (Module.Finite A
        ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
          (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 0))) ∧
      (Module.Finite A
        ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
          (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 1))) ↔
      ∀ y : S.Y, (hy : S.y y ∈ S.U) →
        let yU := closedFiberOpenPoint S y hy
        ∀ z : PointClosure.scheme (S.U.ι yU),
          PointClosure.ι (S.U.ι yU) z ∉ S.U →
            (.some (2 : ℕ∞) : WithBot ℕ∞) <
              (.some (moduleDepth ((S.U.toScheme).presheaf.stalk yU)
                (RingedSpace.stalkModuleCat ((F.obj).obj (op 1)).obj yU)) : WithBot ℕ∞) +
                ringKrullDim ((PointClosure.scheme (S.U.ι yU)).presheaf.stalk z))

/- Remark 52.23.2 (2) -/
@[stacks 0EJT] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.firstStageCohomology_finite_of_finiteLocallyFree_s2_codim :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
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
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (h_stage : IsFiniteLocallyFreeStage F 1)
    (hY : satisfiesSerreConditionS S.Y 2)
    (h_codim : ∀ (Y' : irreducibleComponents S.Y)
      (Z' : irreducibleComponents S.Z)
      (hZY :
        TopologicalSpace.IrreducibleCloseds.map S.z.base S.z.continuous
            (S.Z.irreducibleComponentIrreducibleClosed Z') ≤
          TopologicalSpace.IrreducibleCloseds.map S.y.base S.y.continuous
            (S.Y.irreducibleComponentIrreducibleClosed Y')),
      (3 : ℕ∞) ≤ TopologicalSpace.codimBetween
        (TopologicalSpace.IrreducibleCloseds.map S.z.base S.z.continuous
          (S.Z.irreducibleComponentIrreducibleClosed Z'))
        (TopologicalSpace.IrreducibleCloseds.map S.y.base S.y.continuous
          (S.Y.irreducibleComponentIrreducibleClosed Y')) hZY),
    (Module.Finite A
        ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
          (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 0))) ∧
      (Module.Finite A
        ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
          (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 1))))

end AlgebraicGeometry.Scheme.CoherentFormalModules
