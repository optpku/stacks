/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Inequalities
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.MapAnnihilation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import ReasLib.CategoryTheory.Pro.Presentation

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The points of the open complement lying on the closed fiber at distance at most `k`
from the algebraization closed subset. -/
def depthImprovementLocus (S : AffineAlgebraizationSetup A) (k : ℕ∞) : Set S.U :=
  {x | ∃ (y : S.Y) (hy : S.y y ∈ S.U),
    x = closedFiberOpenPoint S y hy ∧ algebraizationDistance S y ≤ k}

/-- A morphism to a coherent inverse system is a weighted depth-three improvement when
each stage has weighted depth at least three on the closed fiber, is unchanged outside
the distance-two locus, and is stalkwise surjective on the distance-two boundary stratum. -/
def IsDepthThreeImprovement (S : AffineAlgebraizationSetup A)
    {F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)}
    {G : SequentialInverseSystem (RingedSpace.Coh ((S.U.toScheme).toRingedSpace))}
    (α : F.obj ⟶ G) : Prop :=
  (∀ (n : ℕ) (y : S.Y) (hy : S.y y ∈ S.U),
    (3 : ℕ∞) ≤
      moduleDepth ((S.U.toScheme).presheaf.stalk (closedFiberOpenPoint S y hy))
        (RingedSpace.stalkModuleCat (G.obj (op n)).obj (closedFiberOpenPoint S y hy)) +
        algebraizationDistance S y) ∧
    (∀ (n : ℕ) (x : S.U), x ∉ depthImprovementLocus S 2 →
      IsIso (RingedSpace.moduleStalkHom x (α.app (op n)).hom)) ∧
    (∀ (n : ℕ) (x : S.U), x ∈ depthImprovementLocus S 2 →
      x ∉ depthImprovementLocus S 1 →
        Function.Surjective (RingedSpace.moduleStalkMap x (α.app (op n)).hom))

namespace IsDepthThreeImprovement

variable {S : AffineAlgebraizationSetup A}
  {F : CoherentFormalModules S.U.toScheme
    ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)}
  {G G' : SequentialInverseSystem (RingedSpace.Coh ((S.U.toScheme).toRingedSpace))}
  {α : F.obj ⟶ G}

/-- Every stage of a weighted depth-three improvement has weighted stalk depth at least
three at every point of the closed fiber in the open complement. -/
theorem depth (hα : IsDepthThreeImprovement S α)
    (n : ℕ) (y : S.Y) (hy : S.y y ∈ S.U) :
    (3 : ℕ∞) ≤
      moduleDepth ((S.U.toScheme).presheaf.stalk (closedFiberOpenPoint S y hy))
        (RingedSpace.stalkModuleCat (G.obj (op n)).obj (closedFiberOpenPoint S y hy)) +
        algebraizationDistance S y := sorry

/-- A weighted depth-three improvement induces stalk isomorphisms outside the
distance-two locus at every stage. -/
theorem isIso_stalk (hα : IsDepthThreeImprovement S α)
    (n : ℕ) (x : S.U) (hx : x ∉ depthImprovementLocus S 2) :
    IsIso (RingedSpace.moduleStalkHom x (α.app (op n)).hom) := sorry

/-- A weighted depth-three improvement is stalkwise surjective on the distance-two
locus outside the distance-one locus at every stage. -/
theorem surjective_stalk (hα : IsDepthThreeImprovement S α)
    (n : ℕ) (x : S.U) (hx : x ∈ depthImprovementLocus S 2)
    (hx' : x ∉ depthImprovementLocus S 1) :
    Function.Surjective (RingedSpace.moduleStalkMap x (α.app (op n)).hom) := sorry

end IsDepthThreeImprovement

/-- Over a Noetherian ring admitting an intrinsic dualizing complex, a coherent formal
module satisfying the ordinary `(2, 2 + d)` inequalities and a local cohomological
dimension bound `d` admits a weighted depth-three improvement. This improvement is
pro-isomorphic to a coherent formal module with uniformly ideal-power-annihilated
comparison kernels and cokernels, and its cohomology in degrees zero and one is finite
over the ring at every stage. -/
theorem existsDepthThreeImprovement
    (S : AffineAlgebraizationSetup A)
    (h_dualizing : ∃ K : DerivedCategory (ModuleCat.{u} A),
      CategoryTheory.DerivedCategory.IsDualizing K)
    (d : ℤ) (h_cd : Ideal.LocalCohomology.HasDimensionLE S.I d)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_ineq : SatisfiesInequalities S F 2 (2 + d)) :
    ∃ (F'' : SequentialInverseSystem (RingedSpace.Coh ((S.U.toScheme).toRingedSpace)))
      (α : F.obj ⟶ F''),
      IsDepthThreeImprovement S α ∧
        ∃ (H' : CoherentFormalModules S.U.toScheme
            ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
          (e : (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj F'' ≅
            (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj H'.obj)
          (φ : F ⟶ H'),
          (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).map α ≫ e.hom =
              (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).map φ.hom ∧
            Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation
              ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) φ ∧
            ∀ n : ℕ,
              Module.Finite A
                  ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
                    (Scheme.Modules.cohomology (F''.obj (op n)).obj 0)) ∧
                Module.Finite A
                  ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap S.U.ι)).obj
                    (Scheme.Modules.cohomology (F''.obj (op n)).obj 1)) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
