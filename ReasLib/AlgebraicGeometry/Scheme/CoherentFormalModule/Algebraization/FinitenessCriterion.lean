/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.RegularSequence
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.FiniteLocallyFreeStage
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Depth
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- In the regular-sequence affine algebraization setup over a ring with a dualizing
complex, the first stage has finite degree-zero and degree-one cohomology if and
only if its stalk depth plus the local dimension of each boundary point in the
reduced point closure is strictly greater than two. -/
theorem firstStageCohomology_finite_iff_depth_add_pointClosureDim
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
    (h_dualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H) :
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
                ringKrullDim ((PointClosure.scheme (S.U.ι yU)).presheaf.stalk z) := sorry

/-- In the regular-sequence affine algebraization setup over a ring with a dualizing
complex, a finite locally free first stage, Serre's condition `(S₂)` on the closed
fiber, and codimension at least three for every contained pair of boundary and
closed-fiber irreducible components imply finite cohomology in degrees zero and one. -/
theorem firstStageCohomology_finite_of_finiteLocallyFree_s2_codim
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
          (S.Y.irreducibleComponentIrreducibleClosed Y')) hZY) :
    (Module.Finite A
        ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
          (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 0))) ∧
      (Module.Finite A
        ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
          (Scheme.Modules.cohomology ((F.obj).obj (op 1)).obj 1))) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
